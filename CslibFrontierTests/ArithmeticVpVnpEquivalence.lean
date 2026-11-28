/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

import CslibFrontierTests.ArithmeticVpVnpStatement
import CslibFrontier.Computability.Circuit.Arithmetic.VNP
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.AllFields

/-!
# `VP` and `VNP` agree with an independent formalization

The vp-vnp development (`anthropics/formal-math`, folder `vp-vnp`, commit `11b6c7e`) defines
arithmetic circuits and Valiant's classes on its own, from Mathlib alone, and states
`VP ⊂ VNP` over every field as `Statement.Separation`. `ArithmeticVpVnpStatement` holds the
definitions that statement uses, copied line for line from its `Statement.lean`; only the import
differs (`import Mathlib` there). This file proves that the two formalizations agree: over every
commutative semiring, `VP K ⊂ VNP K` holds exactly when `Statement.VP K ⊂ Statement.VNP K` does
(`ssubset_iff`), so the separation stated with this library's `VP` and `VNP` is equivalent to
`Statement.Separation` (`separation_iff`). With the library's proof of `VP F ⊂ VNP F` over every
field (Corollary M.4, `Cslib.Circuits.Arithmetic.VP_ssubset_VNP`), the vp-vnp statement itself
follows (`separation`).

The models differ. Here a circuit is a straight-line program whose size counts its gates but not its
inputs, its variables are `Fin n`, and sizes are bounded by `PolynomiallyBounded`. In vp-vnp a
circuit is a list of polynomials whose length counts the variables too, its variables form any
finite type, and sizes are bounded by `n ^ a + a`. None of this changes the classes: a polynomial
computed within `s` nodes is an entry of a list of length `s` in vp-vnp's sense (the library's
`ComputedWithin.exists_steps`, after raising the bound of `mem_VP_iff` to `n ^ a + a` with
`ComputedWithin.mono`), a list of length `s` gives a circuit of size at most `s`
(`exists_circuit_of_computes`), and renaming variables along bijections preserves membership. So the
translations `toS` and `ofS` of families preserve VP and VNP.
-/

open MvPolynomial Cslib Cslib.Circuits Cslib.Circuits.Arithmetic

universe u

namespace CslibFrontierTests.ArithmeticVpVnpEquivalence

/-- A polynomial bound in the sense of cslib gives a bound `n ^ a + a` valid for every `n`. -/
theorem exists_le_pow_add {f : ℕ → ℕ} (hf : PolynomiallyBounded f) :
    ∃ a, ∀ n, f n ≤ n ^ a + a := by
  obtain ⟨d, hd⟩ := hf
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hd
  refine ⟨d + ∑ k ∈ Finset.range (N + 1), f k, fun n => ?_⟩
  rcases lt_or_ge n (N + 1) with h | h
  · have := Finset.single_le_sum (fun k _ => Nat.zero_le (f k)) (Finset.mem_range.mpr h)
    omega
  · have : f n ≤ n ^ d := hN n (by omega)
    have := Nat.pow_le_pow_right (show 0 < n by omega)
      (Nat.le_add_right d (∑ k ∈ .range (N + 1), f k))
    omega

/-! ### vp-vnp circuits -/

/-- Entry `k` of `l` is a variable, a constant, or the sum or the product of two earlier entries:
the condition on the lists of `Statement.Computes`. -/
abbrev Step {R : Type u} [CommSemiring R] {V : Type} (l : ℕ → MvPolynomial V R) (k : ℕ) : Prop :=
  (∃ v, l k = X v) ∨ (∃ a, l k = C a) ∨ (∃ i < k, ∃ j < k, l k = l i + l j) ∨
    ∃ i < k, ∃ j < k, l k = l i * l j

/-- A step survives renaming the variables of the entries up to it. -/
theorem step_rename {R : Type u} [CommSemiring R] {V W : Type} (e : V → W)
    {l : ℕ → MvPolynomial V R} {l' : ℕ → MvPolynomial W R} {k : ℕ} (h : Step l k)
    (hl : ∀ i ≤ k, l' i = rename e (l i)) : Step l' k := by
  unfold Step
  rcases h with ⟨v, h⟩ | ⟨c, h⟩ | ⟨a, ha, b, hb, h⟩ | ⟨a, ha, b, hb, h⟩ <;> rw [hl k le_rfl, h]
  · exact .inl ⟨e v, rename_X _ _⟩
  · exact .inr <| .inl ⟨c, rename_C _ _⟩
  · exact .inr <| .inr <| .inl ⟨a, ha, b, hb, by rw [map_add, hl a ha.le, hl b hb.le]⟩
  · exact .inr <| .inr <| .inr ⟨a, ha, b, hb, by rw [map_mul, hl a ha.le, hl b hb.le]⟩

theorem computes_rename {R : Type u} [CommSemiring R] {V W : Type} (e : V → W)
    {f : MvPolynomial V R} {s : ℕ} (h : Statement.Computes f s) :
    Statement.Computes (rename e f) s := by
  obtain ⟨l, hl, k, hk, rfl⟩ := h
  exact ⟨fun i => rename e (l i), fun i hi => step_rename e (hl i hi) fun _ _ => rfl, k, hk, rfl⟩

/-- Membership in the vp-vnp class VP survives renaming the variables along bijections. -/
theorem mem_VP_of_equiv {R : Type u} [CommSemiring R] {F G : Statement.Family R}
    (hF : F ∈ Statement.VP R) (e : ∀ n, F.vars n ≃ G.vars n)
    (hG : ∀ n, G.poly n = rename (e n) (F.poly n)) : G ∈ Statement.VP R := by
  obtain ⟨a, ha⟩ := hF
  refine ⟨a, fun n => ⟨?_, ?_, ?_⟩⟩
  · exact Fintype.card_congr (e n) ▸ (ha n).1
  · exact hG n ▸ (totalDegree_rename_le _ _).trans (ha n).2.1
  · exact hG n ▸ computes_rename _ (ha n).2.2

variable {K : Type u} [CommSemiring K] {n : ℕ}

/-! ### From lists to circuits -/

/-- A list of length `s` gives a circuit with at most `s` gates: variables become inputs, and
every other entry one gate. -/
theorem exists_circuit_of_computes {s : ℕ} {p : MvPolynomial (Fin n) K}
    (h : Statement.Computes p s) :
    ∃ c : Circuit (arithSignature K) n 1, c.polynomial 0 = p ∧ c.size ≤ s := by
  obtain ⟨l, hl, k₀, hk₀, rfl⟩ := h
  let F (i : ℕ) (x : Fin n → MvPolynomial (Fin n) K) := aeval x (l i)
  have key (k : ℕ) (hk : k ≤ s) :
      Synthesis (arithInterpretationWith K C) (inputs n) (F '' {i | i < k}) k := by
    induction k with
    | zero => exact Synthesis.of_subset (by simp)
    | succ k ih =>
      have mem {i} (hi : i < k) : F i ∈ inputs n ∪ F '' {i | i < k} := Or.inr ⟨i, hi, rfl⟩
      have step :
          Synthesis (arithInterpretationWith K C) (inputs n ∪ F '' {i | i < k}) {F k} 1 := by
        rcases hl k (by omega) with ⟨v, h⟩ | ⟨c, h⟩ | ⟨a, ha, b, hb, h⟩ | ⟨a, ha, b, hb, h⟩
        · exact (Synthesis.of_mem (Or.inl ⟨v, funext fun x => by simp [F, h]⟩)).mono
            le_rfl le_rfl zero_le_one
        · exact (funext fun x => by simp [F, h, algebraMap_eq] : (fun _ => C c) = F k) ▸
            Synthesis.arith_const c
        · exact (funext fun x => by simp [F, h] : (fun x => F a x + F b x) = F k) ▸
            Synthesis.arith_add (mem ha) (mem hb)
        · exact (funext fun x => by simp [F, h] : (fun x => F a x * F b x) = F k) ▸
            Synthesis.arith_mul (mem ha) (mem hb)
      refine ((ih (by omega)).comp step).mono le_rfl ?_ le_rfl
      rintro _ ⟨i, hi, rfl⟩
      obtain hi | rfl := (show i < k ∨ i = k by have : i < k + 1 := hi; omega)
      · exact .inl ⟨i, hi, rfl⟩
      · exact .inr rfl
  obtain ⟨c, hc, hs⟩ := Synthesis.exists_circuit_polynomial
    ((key s le_rfl).mono le_rfl (Set.singleton_subset_iff.mpr ⟨k₀, hk₀, rfl⟩) le_rfl)
  exact ⟨c, by simp [hc, F, aeval_X_left_apply], hs⟩

/-! ### Translating families -/

/-- A cslib-frontier family as a vp-vnp family, with variables `Fin (f.vars n)`. -/
abbrev toS (f : PolynomialFamily K) : Statement.Family K where
  vars n := Fin (f.vars n)
  poly := f.poly

/-- A vp-vnp family as a cslib-frontier family, its variables numbered. -/
noncomputable abbrev ofS (g : Statement.Family K) : PolynomialFamily K where
  vars n := Fintype.card (g.vars n)
  poly n := rename (Fintype.equivFin (g.vars n)) (g.poly n)

theorem toS_mem_VP {f : PolynomialFamily K} (hf : f ∈ VP K) : toS f ∈ Statement.VP K := by
  obtain ⟨⟨hv, hd⟩, b, hb, hc⟩ := mem_VP_iff.1 hf
  obtain ⟨a, ha⟩ := exists_le_pow_add
    (f := fun n => f.vars n + b n + (f.poly n).totalDegree) ((hv.add hb).add hd)
  refine ⟨a, fun n => ?_⟩
  have := ha n
  refine ⟨by rw [Fintype.card_fin]; omega, show (f.poly n).totalDegree ≤ _ by omega, ?_⟩
  exact ((hc n).mono (show b n ≤ n ^ a + a by omega)).exists_steps

theorem mem_VP_of_toS {f : PolynomialFamily K} (hf : toS f ∈ Statement.VP K) : f ∈ VP K := by
  obtain ⟨a, ha⟩ := hf
  have pb {g : ℕ → ℕ} (h : ∀ n, g n ≤ n ^ a + a) : PolynomiallyBounded g :=
    PolynomiallyBounded.mono_of_le (by fun_prop) h
  choose c hc hs using fun n => exists_circuit_of_computes (ha n).2.2
  exact ⟨⟨pb fun n => by simpa using (ha n).1, pb fun n => (ha n).2.1⟩, c, pb hs, hc⟩

theorem mem_VP_of_ofS {g : Statement.Family K} (hg : ofS g ∈ VP K) : g ∈ Statement.VP K :=
  mem_VP_of_equiv (toS_mem_VP hg) (fun n => (Fintype.equivFin (g.vars n)).symm) fun n => by
    rw [rename_rename, Equiv.symm_comp_self, rename_id_apply]

/-- A Boolean assignment of cslib-frontier substitutes as one of vp-vnp, along
`Fin (N + m) ≃ Fin N ⊕ Fin m`. -/
theorem booleanAssignment_eq {N m : ℕ} (e : Fin m → Bool) :
    (fun i => Sum.elim X (fun a => C a) (booleanAssignment (K := K) (n := N) e i)) =
      Sum.elim X (fun i => if e i then 1 else 0) ∘ finSumFinEquiv.symm := by
  funext i
  induction i using Fin.addCases with
  | left i => simp [booleanAssignment]
  | right j => cases h : e j <;> simp [booleanAssignment, h]

theorem toS_mem_VNP {f : PolynomialFamily K} (hf : f ∈ VNP K) : toS f ∈ Statement.VNP K := by
  obtain ⟨m, g, hg, hfg⟩ := hf
  refine ⟨m, fun n => rename finSumFinEquiv.symm (g n),
    mem_VP_of_equiv (toS_mem_VP hg) (fun n => finSumFinEquiv.symm) (fun n => rfl), fun n => ?_⟩
  change f.poly n = _
  rw [hfg n, booleanSum]
  exact Finset.sum_congr rfl fun e _ => by rw [projection, booleanAssignment_eq, aeval_rename]

theorem ofS_mem_VNP {g : Statement.Family K} (hg : g ∈ Statement.VNP K) : ofS g ∈ VNP K := by
  obtain ⟨r, h, hh, hgh⟩ := hg
  let e (n : ℕ) : g.vars n ⊕ Fin (r n) ≃ Fin (Fintype.card (g.vars n) + r n) :=
    (Equiv.sumCongr (Fintype.equivFin _) (Equiv.refl _)).trans finSumFinEquiv
  refine ⟨r, fun n => rename (e n) (h n), mem_VP_of_toS (mem_VP_of_equiv hh e fun n => rfl),
    fun n => ?_⟩
  change rename _ (g.poly n) = _
  rw [hgh n, map_sum]
  unfold booleanSum
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [projection, booleanAssignment_eq, aeval_rename, ← AlgHom.comp_apply, comp_aeval]
  exact congrArg (aeval · (h n)) (funext fun i => by rcases i with v | j <;> simp [e])

theorem VP_subset_VNP_statement : Statement.VP K ⊆ Statement.VNP K := fun g hg =>
  ⟨fun _ => 0, fun n => rename Sum.inl (g.poly n),
    mem_VP_of_equiv hg (fun n => (Equiv.sumEmpty _ _).symm) (fun n => rfl),
    fun n => by simp [aeval_rename, Function.comp_def, aeval_X_left_apply]⟩

/-! ### The equivalence -/

/-- Over every commutative semiring, VP is a proper subset of VNP in the sense of cslib-frontier
exactly when it is in the sense of the vp-vnp development. -/
theorem ssubset_iff {K : Type u} [CommSemiring K] :
    VP K ⊂ VNP K ↔ Statement.VP K ⊂ Statement.VNP K := by
  rw [Set.ssubset_def, Set.ssubset_def]
  constructor
  · rintro ⟨-, hnot⟩
    exact ⟨VP_subset_VNP_statement, fun hsub =>
      hnot fun f hf => mem_VP_of_toS (hsub (toS_mem_VNP hf))⟩
  · rintro ⟨-, hnot⟩
    exact ⟨VP_subset_VNP, fun hsub => hnot fun g hg => mem_VP_of_ofS (hsub (ofS_mem_VNP hg))⟩

/-- `VP ⊂ VNP` over every field, stated with cslib-frontier's `VP` and `VNP`, is equivalent to
`Statement.Separation` of the vp-vnp development. -/
theorem separation_iff :
    (∀ (K : Type u) [Field K], VP K ⊂ VNP K) ↔ Statement.Separation.{u} :=
  forall_congr' fun _ => forall_congr' fun _ => ssubset_iff

/-- **VP ≠ VNP**, as the vp-vnp formalization states it (`Statement.Separation`): over every field,
its `VP` is a proper subset of its `VNP`. This is the library's Corollary M.4
(`Cslib.Circuits.Arithmetic.VP_ssubset_VNP`) carried over by `separation_iff`. -/
theorem separation : Statement.Separation.{u} :=
  separation_iff.1 fun K _ => VP_ssubset_VNP K

end CslibFrontierTests.ArithmeticVpVnpEquivalence
