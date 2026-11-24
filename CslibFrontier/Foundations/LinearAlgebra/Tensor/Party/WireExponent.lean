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
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Tactic.FinCases

/-!
# Spectral points at unit tensors and wires

Lemma A.2 of *VP ≠ VNP over every field* [AnthropicVPVNP2026]. A spectral point `F` has the value
`q ^ g` at the unit tensor of size `q ≥ 1` with legs at `π a`, where `g` is the *unit exponent*
`F.unitExponent π ≥ 0` (`SpectralPoint.apply_push_unit`). For wires, `g` is the wire exponent
`F.wireExponent p q`. It is a pseudometric with values in `[0, 1]`, and the unit exponent of a set
of parties is at most the sum of the wire exponents along the edges of any tree on them
(`SpectralPoint.unitExponent_le_sum_of_isTree`). Moving the legs of a tensor changes the value of a
spectral point at most by the values at wires between the old and the new positions
(`SpectralPoint.apply_push_le`), and the wire exponents of a pull-back are those of the images
(`SpectralPoint.pull_wireExponent`).

The support point (`SpectralPoint.support`) has wire exponents `0`, and the powers `F ^ s` for
`0 < s ≤ 1` (`SpectralPoint.rpow`, the last example after Definition A.1) have `s` times those of
`F`.

## Main definitions

* `Cslib.PartyTensor.SpectralPoint.unitExponent`: the exponent of the unit tensors with legs `π`.
* `Cslib.PartyTensor.SpectralPoint.rpow`: the power `F ^ s` of a spectral point.

## Main results

* `Cslib.PartyTensor.SpectralPoint.apply_push_unit`, `Cslib.PartyTensor.SpectralPoint.apply_wire`,
  `Cslib.PartyTensor.SpectralPoint.apply_wire_le`.
* `Cslib.PartyTensor.SpectralPoint.wireExponent_nonneg`, `wireExponent_le_one`,
  `wireExponent_self`, `wireExponent_comm`, `wireExponent_triangle`: the wire exponent is a
  pseudometric with values in `[0, 1]`.
* `Cslib.PartyTensor.push_unit_le_prod_wire`: a unit tensor on a connected graph is a restriction of
  the product of the wires on its edges.
* `Cslib.PartyTensor.SpectralPoint.unitExponent_le_sum_of_isTree`: the tree bound.
* `Cslib.PartyTensor.SpectralPoint.apply_push_le`: moving legs.
* `Cslib.PartyTensor.SpectralPoint.pull_wireExponent`,
  `Cslib.PartyTensor.SpectralPoint.wireExponent_support`,
  `Cslib.PartyTensor.SpectralPoint.wireExponent_rpow`.
* `Cslib.PartyTensor.UpperFunctional.push_const_le`: a tensor with all legs at one party.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Lemma A.2 (§A.2) and the examples after Definition A.1 of the paper; modules `Paper.Tensors`
  (`lem_exponents`) and `Ov.Core.Wire`
-/

public section

namespace Cslib.PartyTensor

open Finset

variable {I J A : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype A]
  [DecidableEq A]

section CommSemiring

variable {K : Type} [CommSemiring K]

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
@[expose] noncomputable def unitExponent (π : A → I) : ℝ :=
  Real.logb 2 (F (push π (unit K A 2)))

/-- A wire has no direction. -/
theorem wireExponent_comm (p q : I) : F.wireExponent p q = F.wireExponent q p := by
  rw [wireExponent, wireExponent, F.congr (antisymmRel_wire_comm 2 p q)]

/-- The unit exponent of two parties is their wire exponent. -/
theorem unitExponent_pair (p q : I) :
    F.unitExponent (Subtype.val : ({p, q} : Finset I) → I) = F.wireExponent p q := by
  have h : Set.range ![p, q] = Set.range (Subtype.val : ({p, q} : Finset I) → I) := by
    simp only [Matrix.range_cons, Matrix.range_empty, Subtype.range_coe_subtype]
    ext x
    simp [or_comm]
  rw [unitExponent, wireExponent, wire, F.congr (antisymmRel_push_unit_congr _ _ h 2)]

/-- The wire exponents of a pull-back are those of the images. -/
@[simp] theorem pull_wireExponent (π : J → I) (p q : J) :
    (F.pull π).wireExponent p q = F.wireExponent (π p) (π q) := by
  rw [wireExponent, wireExponent, pull_apply, wire, wire]
  congr 1
  refine F.congr ((antisymmRel_push_push π ![p, q] (unit K (Fin 2) 2)).trans ?_)
  have : π ∘ ![p, q] = ![π p, π q] := by funext i; fin_cases i <;> rfl
  rw [this]

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

@[simp] theorem rpow_apply (s : ℝ) (h0 : 0 < s) (h1 : s ≤ 1) (t : PartyTensor K I) :
    F.rpow s h0 h1 t = F t ^ s := by
  rfl

end SpectralPoint

/-- An upper functional is at most `1` at a tensor with all its legs at one party. -/
theorem UpperFunctional.push_const_le (P : UpperFunctional K I) (q : I) (t : PartyTensor K J) :
    P (push (fun _ => q) t) ≤ 1 :=
  P.map_one ▸ P.monotone (push_const_le_one q t)

end CommSemiring

section Field

variable {K : Type} [Field K]

namespace SpectralPoint

variable (F : SpectralPoint K I)

theorem unitExponent_nonneg [Nonempty I] (π : A → I) : 0 ≤ F.unitExponent π :=
  Real.logb_nonneg (by norm_num) (F.one_le_unit π (by norm_num))

/-- **Paper: Lemma A.2**, the unit tensors: `F` at the unit tensor of size `q ≥ 1` with legs `π` is
`q` to the unit exponent. As in the paper's proof, `q ↦ F ⟨q⟩` is at least `1`, multiplicative and
monotone, hence a power of `q`. -/
theorem apply_push_unit [Nonempty I] (π : A → I) {q : ℕ} (hq : 1 ≤ q) :
    F (push π (unit K A q)) = (q : ℝ) ^ F.unitExponent π :=
  eq_rpow_of_mul_monotone (fun n => F (push π (unit K A n))) (fun _ h => F.one_le_unit π h)
    (fun m n _ _ => by
      rw [F.congr ((antisymmRel_unit_mul m n).image (monotone_push π)),
        F.congr (antisymmRel_push_mul _ _ _), F.map_mul])
    (fun _ _ _ h => F.monotone (push_le_push π (unit_le_unit h))) _ hq

/-- At a wire of dimension `n ≥ 1`, a spectral point is `n` to the wire exponent. -/
theorem apply_wire (p q : I) {n : ℕ} (hn : 1 ≤ n) :
    F (wire K n p q) = (n : ℝ) ^ F.wireExponent p q :=
  have : Nonempty I := ⟨p⟩
  F.apply_push_unit ![p, q] hn

theorem apply_wire_two (p q : I) : F (wire K 2 p q) = 2 ^ F.wireExponent p q := by
  exact_mod_cast F.apply_wire p q (n := 2) (by norm_num)

/-- A spectral point at a wire of dimension `n` is at most `n` to the wire exponent, also for
`n = 0`. -/
theorem apply_wire_le (p q : I) (n : ℕ) : F (wire K n p q) ≤ (n : ℝ) ^ F.wireExponent p q := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h : F (wire K 0 p q) ≤ ((0 : ℕ) : ℝ) := F.unit_le ![p, q] 0
    refine h.trans ?_
    rw [Nat.cast_zero]
    exact Real.rpow_nonneg le_rfl _
  · exact (F.apply_wire p q hn).le

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

/-- **Paper: Lemma A.2**, the triangle inequality. As in the paper's proof, contracting the two
indices at `q` shows that the wire from `p` to `r` is a restriction of the product of the wires from
`p` to `q` and from `q` to `r`. -/
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

/-- **Paper: Lemma A.2**, the tree bound: the unit exponent of a set `P` of parties is at most the
sum of the wire exponents along the edges of any tree on `P`. -/
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

/-- Moving legs: if the leg `j` moves from `π' j` to `π j`, the value grows at most by the values
of the wires from `π j` to `π' j` of the dimensions of the legs. -/
theorem apply_push_le (π π' : J → I) (t : PartyTensor K J) :
    F (push π t) ≤
      (∏ j, (Fintype.card (t.Index j) : ℝ) ^ F.wireExponent (π j) (π' j)) * F (push π' t) := by
  refine (F.le_mul (push_le_mul_push π π' t)).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (F.nonneg _)
  rw [F.map_prod]
  exact Finset.prod_le_prod₀ (fun _ _ => F.nonneg _) fun j _ => F.apply_wire_le _ _ _

/-- The support point has wire exponent `0`. -/
theorem wireExponent_support (p q : I) : (support K I).wireExponent p q = 0 := by
  have : Nonempty I := ⟨p⟩
  have hle : support K I (wire K 2 p q) ≤ 1 := by
    rw [support_apply]
    split_ifs <;> norm_num
  rw [wireExponent, le_antisymm hle ((support K I).one_le_unit ![p, q] (by norm_num)),
    Real.logb_one]

/-- The wire exponents of `F ^ s` are `s` times those of `F`. -/
theorem wireExponent_rpow (s : ℝ) (h0 : 0 < s) (h1 : s ≤ 1) (p q : I) :
    (F.rpow s h0 h1).wireExponent p q = s * F.wireExponent p q := by
  have : Nonempty I := ⟨p⟩
  have hpos : 0 < F (wire K 2 p q) := zero_lt_one.trans_le (F.one_le_unit ![p, q] (by norm_num))
  rw [wireExponent, wireExponent, rpow_apply, Real.logb_rpow_eq_mul_logb_of_pos hpos]

end SpectralPoint

end Field

end Cslib.PartyTensor
