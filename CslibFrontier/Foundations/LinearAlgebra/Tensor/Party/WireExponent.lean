/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.LinearAlgebra.Tensor.Party.Unit
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
import CslibFrontier.Foundations.Analysis.SpecialFunctions.MulMonotonePow
import CslibFrontier.Foundations.LinearAlgebra.Tensor.Party.Network
import Mathlib.Analysis.MeanInequalitiesPow

/-!
# Spectral points at unit tensors and wires

Lemma A.2 (lem:exponents) of *VP ≠ VNP over every field* [AnthropicVPVNP2026]. A spectral point `F`
has the value `q ^ g` at the unit tensor of size `q ≥ 1` with legs at `π a`, where `g` is the
*unit exponent* `F.unitExponent π ≥ 0` (`SpectralPoint.apply_push_unit`). For wires, `g` is the
wire exponent `F.wireExponent p q`. It is a pseudometric with values in `[0, 1]`, and the unit
exponent of a set of parties is at most the sum of the wire exponents along the edges of any tree
on them (`SpectralPoint.unitExponent_le_sum_of_isTree`).

Two examples follow Definition A.1: the *support point*, `1` on nonzero tensors and `0` on `0`
(`SpectralPoint.support`), and the powers `F ^ s` for `0 < s ≤ 1` (`SpectralPoint.rpow`).

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], modules `Paper.Tensors` and `Ov.Core.Wire`.

## Main definitions

* `Cslib.PartyTensor.SpectralPoint.unitExponent`: the exponent of the unit tensors with legs `π`.
* `Cslib.PartyTensor.SpectralPoint.support`, `Cslib.PartyTensor.SpectralPoint.rpow`.

## Main results

* `Cslib.PartyTensor.SpectralPoint.apply_push_unit`, `Cslib.PartyTensor.SpectralPoint.apply_wire`.
* `Cslib.PartyTensor.SpectralPoint.wireExponent_nonneg`, `wireExponent_le_one`,
  `wireExponent_self`, `wireExponent_comm`, `wireExponent_triangle`: the wire exponent is a
  pseudometric with values in `[0, 1]`.
* `Cslib.PartyTensor.push_unit_le_prod_wire`: a unit tensor on a connected graph is a restriction of
  the product of the wires on its edges.
* `Cslib.PartyTensor.SpectralPoint.unitExponent_le_sum_of_isTree`: the tree bound.
-/

@[expose] public section

namespace Cslib.PartyTensor

open Finset

variable {K : Type} [Field K] {I J A : Type} [Fintype I] [DecidableEq I] [Fintype J]
  [DecidableEq J] [Fintype A] [DecidableEq A]

/-- A unit tensor whose legs `π` follow a connected graph (with edges from `a e` to `b e`) is a
restriction of the product of the wires on the edges. Of the graph only connectedness is used: a
function to `Fin q` that is constant along the edges is constant. -/
theorem push_unit_le_prod_wire {E : Type} [Fintype E] [DecidableEq E] [Nonempty A] (q : ℕ)
    (π : A → I) (a b : E → A)
        (hconn : ∀ f : A → Fin q, (∀ e, f (a e) = f (b e)) → ∀ p p', f p = f p') :
    push π (unit K A q) ≤ prod fun e => wire K q (π (a e)) (π (b e)) := by
  classical
  have key := push_le_of_edges π (ξ := fun o : Option A => o.elim (π (Classical.arbitrary A)) π)
    (unit K A q) (fun _ : E => Fin q) (fun e => some (a e)) (fun e => some (b e))
    (fun o x l => o.elim 1 fun p => ∏ e, if a e = p ∨ b e = p then
      (if l e = x p then (1 : K) else 0) else 1)
    (by
      rintro (_ | p) x x' l l' hx hl
      · rfl
      · refine Finset.prod_congr rfl fun e _ => ?_
        by_cases he : a e = p ∨ b e = p
        · have h2 : l e = l' e := hl e (he.imp (congrArg some) (congrArg some))
          have h3 : x p = x' p := hx p rfl
          rw [ite_eq_left he, ite_eq_left he, h2, h3]
        · rw [ite_eq_right he, ite_eq_right he])
    (by
      intro x
      refine Eq.trans ?_ (Fintype.sum_eq_single (fun e => (x (a e) : Fin q)) ?_).symm
      · rw [Fintype.prod_option]
        change _ = 1 * _
        rw [one_mul]
        by_cases h : ∀ i j, x i = x j
        · rw [unit_entry_of h]
          refine (Finset.prod_eq_one fun p _ => Finset.prod_eq_one fun e _ => ?_).symm
          exact ite_eq_right_iff.2 fun _ => ite_eq_left (h (a e) p)
        · rw [unit_entry_of_not h]
          obtain ⟨e, he⟩ : ∃ e, x (a e) ≠ x (b e) := by
            by_contra hne
            push Not at hne
            exact h (hconn x hne)
          refine (Finset.prod_eq_zero (Finset.mem_univ (b e))
            (Finset.prod_eq_zero (Finset.mem_univ e) ?_)).symm
          exact (ite_eq_left (Or.inr rfl)).trans (ite_eq_right he)
      · intro l hl
        obtain ⟨e, he⟩ := Function.ne_iff.1 hl
        refine Finset.prod_eq_zero (Finset.mem_univ (some (a e)))
          (Finset.prod_eq_zero (Finset.mem_univ e) ?_)
        exact (ite_eq_left (Or.inl rfl)).trans (ite_eq_right he))
  simpa only [Fintype.card_fin, Option.elim_some] using key

namespace SpectralPoint

variable (F : SpectralPoint K I)

/-- The *unit exponent* of `F` at the legs `π`: `log₂` of its value at the unit tensor of size `2`
with a leg at `π a` for every `a` (the `g_φ` of Lemma A.2). -/
noncomputable def unitExponent (π : A → I) : ℝ :=
  Real.logb 2 (F (push π (unit K A 2)))

theorem unitExponent_nonneg [Nonempty I] (π : A → I) : 0 ≤ F.unitExponent π :=
  Real.logb_nonneg (by norm_num) (F.one_le_unit π (by norm_num))

/-- **Paper: proof of Lemma lem:exponents.** "The function `q ↦ φ(⟨q⟩_P)` is at least `1`,
multiplicative and monotone, hence a power of `q`." -/
theorem apply_push_unit [Nonempty I] (π : A → I) {q : ℕ} (hq : 1 ≤ q) :
    F (push π (unit K A q)) = (q : ℝ) ^ F.unitExponent π :=
  eq_rpow_of_mul_monotone (fun n => F (push π (unit K A n))) (fun _ h => F.one_le_unit π h)
    (fun m n _ _ => by
      rw [F.congr ((antisymmRel_unit_mul m n).image (monotone_push π)),
        F.congr (antisymmRel_push_mul _ _ _), F.map_mul])
    (fun _ _ _ h => F.monotone (push_le_push π (unit_le_unit h))) _ hq

/-- At a wire of dimension `q ≥ 1`, a spectral point is `q` to the wire exponent. -/
theorem apply_wire (p q : I) {n : ℕ} (hn : 1 ≤ n) :
    F (wire K n p q) = (n : ℝ) ^ F.wireExponent p q :=
  have : Nonempty I := ⟨p⟩
  F.apply_push_unit ![p, q] hn

theorem apply_wire_two (p q : I) : F (wire K 2 p q) = 2 ^ F.wireExponent p q := by
  exact_mod_cast F.apply_wire p q (n := 2) (by norm_num)

theorem wireExponent_nonneg (p q : I) : 0 ≤ F.wireExponent p q :=
  have : Nonempty I := ⟨p⟩
  F.unitExponent_nonneg ![p, q]

/-- A wire of dimension `q` is covered by `q` copies of `1`, so the wire exponent is at most `1`. -/
theorem wireExponent_le_one (p q : I) : F.wireExponent p q ≤ 1 := by
  have : Nonempty I := ⟨p⟩
  have h : F (wire K 2 p q) ≤ (2 : ℕ) := F.unit_le ![p, q] 2
  rw [apply_wire_two] at h
  have h2 : (2 : ℝ) ^ F.wireExponent p q ≤ 2 ^ (1 : ℝ) := by simpa using h
  exact (Real.rpow_le_rpow_left_iff (by norm_num)).1 h2

/-- A wire from a party to itself is a restriction of `1`. -/
theorem wireExponent_self (p : I) : F.wireExponent p p = 0 := by
  have : Nonempty I := ⟨p⟩
  have h : F (wire K 2 p p) = 1 :=
    le_antisymm (F.map_one ▸ F.monotone (wire_self_le_one 2 p))
        (F.one_le_unit ![p, p] (by norm_num))
  rw [wireExponent, h, Real.logb_one]

/-- A wire has no direction. -/
theorem wireExponent_comm (p q : I) : F.wireExponent p q = F.wireExponent q p := by
  rw [wireExponent, wireExponent, F.congr (antisymmRel_wire_comm 2 p q)]

/-- **Paper: proof of Lemma lem:exponents.** "Contracting the two indices at `v` shows that `⟨q⟩_uw`
is a restriction of `⟨q⟩_uv ⟨q⟩_vw` … this is the triangle inequality." -/
theorem wireExponent_triangle (p q r : I) :
    F.wireExponent p r ≤ F.wireExponent p q + F.wireExponent q r := by
  have h := F.le_mul (wire_le_mul_wire (K := K) 2 p r q)
  rw [apply_wire_two, apply_wire_two, apply_wire_two, ← Real.rpow_add (by norm_num)] at h
  exact (Real.rpow_le_rpow_left_iff (by norm_num)).1 h

/-- The unit exponent of the legs of a connected graph is at most the sum of the wire exponents
along its edges. -/
theorem unitExponent_le_sum_wireExponent [Nonempty I] {E : Type} [Fintype E] [Nonempty A]
    (π : A → I) (a b : E → A)
    (hconn : ∀ f : A → Fin 2, (∀ e, f (a e) = f (b e)) → ∀ p p', f p = f p') :
    F.unitExponent π ≤ ∑ e, F.wireExponent (π (a e)) (π (b e)) := by
  classical
  rw [unitExponent, Real.logb_le_iff_le_rpow (by norm_num)
    (zero_lt_one.trans_le (F.one_le_unit π (by norm_num)))]
  refine (F.le_prod (push_unit_le_prod_wire 2 π a b hconn)).trans (le_of_eq ?_)
  rw [Real.rpow_sum_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact Finset.prod_congr rfl fun e _ => F.apply_wire_two _ _

/-- The unit exponent of two parties is their wire exponent. -/
theorem unitExponent_pair (p q : I) :
    F.unitExponent (Subtype.val : ({p, q} : Finset I) → I) = F.wireExponent p q := by
  have h : Set.range ![p, q] = Set.range (Subtype.val : ({p, q} : Finset I) → I) := by
    simp only [Matrix.range_cons, Matrix.range_empty, Subtype.range_coe_subtype]
    ext x
    simp [or_comm]
  rw [unitExponent, wireExponent, wire, F.congr (antisymmRel_push_unit_congr _ _ h 2)]

/-- **Paper: Lemma lem:exponents, the tree bound.** "`g_φ(P) ≤ ∑ d_φ(e)` over the edges of any tree
on `P`." -/
theorem unitExponent_le_sum_of_isTree (P : Finset I) (G : SimpleGraph P) [DecidableRel G.Adj]
    (hT : G.IsTree) :
    F.unitExponent (Subtype.val : P → I) ≤ ∑ e ∈ G.edgeFinset,
      Sym2.lift ⟨fun u v => F.wireExponent u v, fun _ _ => F.wireExponent_comm _ _⟩
        (e.map Subtype.val) := by
  classical
  have : Nonempty P := hT.connected.nonempty
  have : Nonempty I := ⟨(Classical.arbitrary P).1⟩
  refine (F.unitExponent_le_sum_wireExponent (Subtype.val : P → I) (E := G.edgeFinset)
    (fun e => e.1.out.1) (fun e => e.1.out.2) fun f hf p q => ?_).trans (le_of_eq ?_)
  · obtain ⟨w⟩ := hT.connected.preconnected p q
    induction w with
    | nil => rfl
    | @cons u v _ hadj _ ih =>
      refine Eq.trans ?_ ih
      have hmem : s(u, v) ∈ G.edgeFinset := SimpleGraph.mem_edgeFinset.2 hadj
      have h1 : f (s(u, v) : Sym2 P).out.1 = f (s(u, v) : Sym2 P).out.2 := hf ⟨_, hmem⟩
      have h2 : (s((s(u, v) : Sym2 P).out.1, (s(u, v) : Sym2 P).out.2) : Sym2 P) = s(u, v) :=
        Quot.out_eq _
      rcases Sym2.eq_iff.1 h2 with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2] at h1
      exacts [h1, h1.symm]
  · rw [← Finset.sum_coe_sort G.edgeFinset]
    refine Finset.sum_congr rfl fun e _ => ?_
    conv_rhs => rw [← Quot.out_eq e.1]
    rfl

/-! ### Examples of spectral points -/

private theorem entry_eq_zero_of_coveredBy {κ : Type} [Fintype κ] {s : PartyTensor K I}
    {b : κ → PartyTensor K I} (h : s.CoveredBy b) (hb : ∀ k y, (b k).entry y = 0) (x) :
    s.entry x = 0 := by
  obtain ⟨L, hL⟩ := h
  rw [hL x]
  exact Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun y _ => by simp [hb k y]

open Classical in
/-- The *support point*: `1` at every tensor with a nonzero entry and `0` at the zero tensor (the
first example after Definition A.1). -/
noncomputable def support (K : Type) [Field K] (I : Type) [Fintype I] [DecidableEq I] :
    SpectralPoint K I where
  toFun t := if ∃ x, t.entry x ≠ 0 then 1 else 0
  nonneg t := by split_ifs <;> norm_num
  map_one := ite_eq_left ⟨fun _ => (), one_ne_zero⟩
  map_mul s t := by
    have key : (∃ z, (s * t).entry z ≠ 0) ↔ (∃ x, s.entry x ≠ 0) ∧ ∃ y, t.entry y ≠ 0 := by
      constructor
      · rintro ⟨z, hz⟩
        rw [mul_entry] at hz
        exact ⟨⟨_, left_ne_zero_of_mul hz⟩, _, right_ne_zero_of_mul hz⟩
      · rintro ⟨⟨x, hx⟩, y, hy⟩
        exact ⟨fun p => (x p, y p), mul_ne_zero hx hy⟩
    by_cases hs : ∃ x, s.entry x ≠ 0 <;> by_cases ht : ∃ y, t.entry y ≠ 0 <;> simp [key, hs, ht]
  le_sum s b h := by
    have h0 : ∀ k, (0 : ℝ) ≤ if ∃ x, (b k).entry x ≠ 0 then 1 else 0 := fun k => by
      split_ifs <;> norm_num
    split_ifs with hs
    · by_contra hlt
      obtain ⟨x, hx⟩ := hs
      refine hx (entry_eq_zero_of_coveredBy h (fun k y => ?_) x)
      by_contra hy
      have := Finset.single_le_sum (fun k _ => h0 k) (Finset.mem_univ k)
      rw [ite_eq_left ⟨y, hy⟩] at this
      linarith
    · exact Finset.sum_nonneg fun k _ => h0 k

/-- The power `F ^ s` of a spectral point, for `0 < s ≤ 1` (the last example after Definition
A.1). -/
noncomputable def rpow (s : ℝ) (h0 : 0 < s) (h1 : s ≤ 1) : SpectralPoint K I where
  toFun t := F t ^ s
  nonneg t := Real.rpow_nonneg (F.nonneg t) s
  map_one := by rw [F.map_one, Real.one_rpow]
  map_mul a b := by rw [F.map_mul, Real.mul_rpow (F.nonneg a) (F.nonneg b)]
  le_sum {κ} _ a b h := by
    classical
    refine (Real.rpow_le_rpow (F.nonneg a) (F.le_sum a b h) h0.le).trans ?_
    have key : ∀ S : Finset κ, (∑ k ∈ S, F (b k)) ^ s ≤ ∑ k ∈ S, F (b k) ^ s := by
      intro S
      induction S using Finset.induction_on with
      | empty => simp [Real.zero_rpow h0.ne']
      | insert k S hk ih =>
        rw [Finset.sum_insert hk, Finset.sum_insert hk]
        exact (Real.rpow_add_le_add_rpow (F.nonneg _) (Finset.sum_nonneg fun _ _ => F.nonneg _)
          h0.le h1).trans (by gcongr)
    exact key Finset.univ

end SpectralPoint

end Cslib.PartyTensor
