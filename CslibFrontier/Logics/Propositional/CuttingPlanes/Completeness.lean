/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CuttingPlanes
import Mathlib.Tactic.LinearCombination
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Instances.Int
import Mathlib.Topology.Order.OrderClosed

/-!
# Completeness of cutting planes

Every system `Γ` of integer linear inequalities (`Cslib.Logic.PL.Ineq`) without a 0/1 solution has
a cutting planes refutation
(`Cslib.Logic.PL.CuttingPlanes.exists_refutableInSize_of_not_exists_holds`). With soundness, `Γ` is
refutable iff it has no 0/1 solution
(`Cslib.Logic.PL.CuttingPlanes.exists_refutableInSize_iff_not_exists_holds`). The system may be
infinite and over any type of variables; the refutations may be exponentially long.

Completeness of cutting planes over nonempty bounded polyhedra goes back to
[Chvátal][Chvatal1973]. The proof here is this module's own route, specific to 0/1 solutions:
compactness reduces to a finite system, a clause excluding each assignment is derived from an
inequality that the assignment falsifies, and a decision tree eliminates the variables. Its merge
steps are resolution steps, carried out by addition and division by `2` as in the simulation of
resolution by cutting planes
([Cook, Coullard and Turán, Section 3, pp. 34–35][CookCoullardTuran1987]).

1. **Compactness.** The 0/1 solutions of an inequality form a closed subset of the compact space
   `V → Bool`, since an inequality mentions finitely many variables. So some finite subsystem of
   `Γ` has no 0/1 solution, and it suffices to refute a finite `Γ`.
2. **The clause excluding `σ`.** Let `S` be the finite set of variables with a nonzero coefficient
   in `Γ`, and `σ` an assignment. Some `I = (∑ᵥ aᵥ xᵥ ≥ b) ∈ Γ` fails under `σ`, by
   `d = b - ∑ᵥ aᵥ σ(v) ≥ 1`. For each `v ∈ S` let `ℓᵥ` be the literal on `v` that is false under
   `σ`, with inequality `ℓᵥ ≥ 0` (`Cslib.Logic.PL.Literal.toIneq`) of coefficient `eᵥ = ±1`. With
   `M = ∑_{v ∈ S} |aᵥ| + d`, adding `(M - aᵥ eᵥ) • (ℓᵥ ≥ 0)` to `I` for every `v ∈ S` gives an
   inequality with the coefficients of `M • ∑_{v ∈ S} ℓᵥ`. Every axiom added is tight at `σ`, so
   the slack at `σ` is still `-d`, and rounded division by `M ≥ d` gives exactly the inequality
   `∑_{v ∈ S} ℓᵥ ≥ 1` of the clause `⋁_{v ∈ S} ℓᵥ` (`Cslib.Logic.PL.Clause.toIneq`). This uses
   only the axioms for literals false under `σ`: the literals true under `σ` are weakened away
   implicitly, since their coefficients are brought to the right multiple of `M` directly.
3. **Elimination.** If the line `I + ∑_{v ∈ W} (ℓᵥ ≥ 0)`, with `ℓᵥ` the literal on `v` false
   under `τ`, is derivable for every assignment `τ`, then so is `I`. Two siblings `L + (x ≥ 0)` and
   `L + (¬x ≥ 0)`, with `L = I + ∑_{v ∈ T} ℓᵥ`, add up to `2 • L - (0 ≥ 1)`, and division by `2`
   gives `L`; eliminating the variables of `W` one at a time leaves `I`. With `I = (0 ≥ 1)` and
   `W = S`, the leaves are the clauses of step 2, and this refutes `Γ`.

**Implicational completeness.** Over a nonempty type of variables, every inequality
`I = (A ≥ b)` satisfied by all 0/1 solutions of `Γ` is derivable from `Γ`
(`Cslib.Logic.PL.CuttingPlanes.exists_derivableInSize_of_forall_holds`), so `I` is derivable iff
`Γ` implies it over 0/1 assignments
(`Cslib.Logic.PL.CuttingPlanes.exists_derivableInSize_iff_forall_holds`). Over 0/1 assignments
the axioms `xᵥ ≥ 0` and `-xᵥ ≥ -1` bound the solutions, the setting of
[Chvátal][Chvatal1973]'s completeness theorem for nonempty bounded polyhedra; with a variable they
also derive `0 ≥ -1`, so the theorem holds as well for a `Γ` with no 0/1 solution.
[Cook, Coullard and Turán, Section 1, pp. 26–27][CookCoullardTuran1987] work with indirect proofs
of an inequality: refutations of the system together with its negation. Here such a refutation
is used only in step 1, to find finitely many hypotheses; the rest is a direct derivation of the
exact line `I`, with no weakening rule, by a decision tree as in refutation completeness.

1. **Compactness.** `Γ` with `¬I = (-A ≥ 1 - b)` has no 0/1 solution, so it has a refutation, and
   the finitely many hypotheses `Γ₀ ⊆ Γ` among its lines already imply `I`. Let `W` be the
   variables of `Γ₀` and `A`.
2. **Base.** `A ≥ c₀` is a sum of multiples of literal axioms, plus `0 ≥ -1`.
3. **Step `A ≥ c` to `A ≥ c + 1` for `c < b`**, by eliminating the variables of `W` from the
   lines `A + ∑_{v ∈ W} ℓᵥ ≥ c + 1` at the leaves `τ`, as in step 3 of refutation completeness.
   If `τ` falsifies some `J ∈ Γ₀`, add `A ≥ c` to the clause excluding `τ`, derived from `J` as
   in step 2; otherwise `A(τ) ≥ b > c`, and with `d = ∑_{v ∈ W} |aᵥ| + A(τ) - c + 1`, adding
   `(d + aᵥ eᵥ) • (ℓᵥ ≥ 0)` to `(d - 1) • (A ≥ c)` and dividing by `d` gives the line.
4. **Iteration.** Start from `min c₀ b`, lowering `c₀` by multiples of `0 ≥ -1`, and step up to
   `b`.

The axiom `0 ≥ -1 = (xᵥ ≥ 0) + (-xᵥ ≥ -1)` needs a variable. Over an empty type of variables every
line is `0 ≥ b`, and the empty system implies `0 ≥ 0` but derives nothing, so the hypothesis
`Nonempty V` cannot be dropped.

## Main results

* `Cslib.Logic.PL.CuttingPlanes.exists_refutableInSize_of_not_exists_holds`: refutation
  completeness.
* `Cslib.Logic.PL.CuttingPlanes.exists_refutableInSize_iff_not_exists_holds`: a system is
  refutable iff it has no 0/1 solution.
* `Cslib.Logic.PL.CuttingPlanes.exists_derivableInSize_of_forall_holds`: implicational
  completeness.
* `Cslib.Logic.PL.CuttingPlanes.exists_derivableInSize_iff_forall_holds`: an inequality is
  derivable iff it holds at every 0/1 solution of the system.

## References

* [V. Chvátal, *Edmonds polytopes and a hierarchy of combinatorial problems*][Chvatal1973]
* [W. Cook, C. R. Coullard, Gy. Turán, *On the complexity of cutting-plane
  proofs*][CookCoullardTuran1987]
-/

public section

namespace Cslib.Logic.PL.CuttingPlanes

open Finset Ineq

variable {V : Type*} {Γ : Set (Ineq V)}

/-! ### The clause excluding an assignment -/

/-- The literal on `v` that is false under `σ`. -/
private def falseLit (σ : V → Bool) (v : V) : Literal V := (v, !σ v)

/-- The coefficient `±1` of `v` in the inequality of `falseLit σ v`. -/
private def sgn (σ : V → Bool) (v : V) : ℤ := bif σ v then -1 else 1

private theorem coeff_falseLit (σ : V → Bool) (v : V) :
    (falseLit σ v).toIneq.coeff = Finsupp.single v (sgn σ v) := by
  cases h : σ v <;> simp [falseLit, sgn, h, Literal.toIneq]

private theorem sgn_mul_self (σ : V → Bool) (v : V) : sgn σ v * sgn σ v = 1 := by
  cases h : σ v <;> simp [sgn, h]

/-- The inequality of a literal false under `σ` is tight at `σ`. -/
private theorem lhs_falseLit (σ : V → Bool) (v : V) :
    (falseLit σ v).toIneq.lhs σ = (falseLit σ v).toIneq.bound := by
  cases h : σ v <;>
    simp [falseLit, h, Literal.toIneq, Ineq.nonneg, Ineq.leOne, -Finsupp.single_neg]

/-- **The clause excluding `σ`**: from an inequality `I` that fails under `σ` and whose variables
lie in `S`, the inequality `∑_{v ∈ S} ℓᵥ ≥ 1` of the literals `ℓᵥ` false under `σ` is derivable,
by adding multiples of their axioms and one rounded division. -/
private theorem derivableInSize_excl {I : Ineq V} {S : Finset V} (hS : I.coeff.support ⊆ S)
    {σ : V → Bool} (hσ : ¬ I.Holds σ) {s : ℕ} (hI : DerivableInSize Γ I s) :
    DerivableInSize Γ (contra + ∑ v ∈ S, (falseLit σ v).toIneq) (s + #S * 3 + 1) := by
  classical
  set d : ℤ := I.bound - I.lhs σ with hd_def
  have hd : 0 < d := by rw [Holds, not_le] at hσ; omega
  set A : ℤ := ∑ v ∈ S, |I.coeff v|
  have hA : 0 ≤ A := sum_nonneg fun v _ => abs_nonneg _
  set M : ℕ := (A + d).toNat
  have hM : (M : ℤ) = A + d := Int.toNat_of_nonneg (by omega)
  have hM0 : 0 < M := by omega
  have hle : ∀ v ∈ S, I.coeff v * sgn σ v ≤ A := fun v hv => by
    refine le_trans ?_ (single_le_sum (f := fun v => |I.coeff v|) (fun _ _ => abs_nonneg _) hv)
    cases h : σ v <;> simp [sgn, h, le_abs_self, neg_le_abs]
  set k : V → ℕ := fun v => ((M : ℤ) - I.coeff v * sgn σ v).toNat
  have hk : ∀ v ∈ S, (k v : ℤ) = M - I.coeff v * sgn σ v := fun v hv =>
    Int.toNat_of_nonneg (by have := hle v hv; omega)
  have hk0 : ∀ v ∈ S, 0 < k v := fun v hv => by have := hle v hv; have := hk v hv; omega
  set K : Ineq V := contra + ∑ v ∈ S, (falseLit σ v).toIneq
  set J : Ineq V := I + ∑ v ∈ S, k v • (falseLit σ v).toIneq
  have hJ : DerivableInSize Γ J (s + #S * (2 + 1)) :=
    hI.add_sum S fun v hv => (DerivableInSize.literal _).smul _ (hk0 v hv)
  have hcoeff : J.coeff = (M : ℤ) • K.coeff := by
    ext w
    simp only [J, K, coeff_add, coeff_sum, coeff_nsmul, coeff_contra, coeff_falseLit,
      Finsupp.add_apply, Finset.sum_apply', Finsupp.smul_apply, Finsupp.single_apply,
      zero_add, smul_eq_mul, Finsupp.smul_single, sum_ite_eq']
    by_cases hw : w ∈ S
    · simp only [hw, ite_true]
      linear_combination (-I.coeff w) * sgn_mul_self σ w + sgn σ w * hk w hw
    · have : I.coeff w = 0 := Finsupp.notMem_support_iff.1 fun h => hw (hS h)
      simp [hw, this]
  have hlhsK : K.lhs σ = K.bound - 1 := by
    simp only [K, lhs_add, lhs_sum, bound_add, bound_sum, lhs_falseLit, bound_contra]
    simp [lhs_eq_finsuppSum]
  have hlhsJ : J.lhs σ = I.lhs σ + ∑ v ∈ S, (k v : ℤ) * (falseLit σ v).toIneq.bound := by
    simp only [J, lhs_add, lhs_sum, lhs_nsmul, lhs_falseLit]
  have hboundJ : J.bound = I.bound + ∑ v ∈ S, (k v : ℤ) * (falseLit σ v).toIneq.bound := by
    simp only [J, bound_add, bound_sum, bound_nsmul, nsmul_eq_mul]
  have hJK : J.lhs σ = M * (K.bound - 1) := hlhsK ▸ lhs_of_coeff_eq_smul σ hcoeff
  have hdiv : J.div M = K := by
    refine div_eq_of hM0 hcoeff ?_ ?_ <;> linarith
  have := hJ.div M hM0 fun v => by rw [hcoeff]; exact ⟨_, rfl⟩
  rw [hdiv] at this
  exact this

/-! ### Eliminating variables by a decision tree -/

/-- **Merging two siblings** of the decision tree on `x`: the lines `L + (x ≥ 0)` and
`L + (¬x ≥ 0)`, with `L = I + ∑_{v ∈ T} ℓᵥ`, add up to `2 • L - (0 ≥ 1)`, and rounded division
by `2` gives `L`. -/
private theorem exists_derivableInSize_merge [DecidableEq V] {I : Ineq V} {T : Finset V}
    {x : V} (hx : x ∉ T) {τ : V → Bool}
    (h : ∀ τ' : V → Bool,
      ∃ t, DerivableInSize Γ (I + ∑ v ∈ insert x T, (falseLit τ' v).toIneq) t) :
    ∃ t, DerivableInSize Γ (I + ∑ v ∈ T, (falseLit τ v).toIneq) t := by
  set τ' := Function.update τ x (!τ x)
  set L : Ineq V := I + ∑ v ∈ T, (falseLit τ v).toIneq
  have hT : ∑ v ∈ T, (falseLit τ' v).toIneq = ∑ v ∈ T, (falseLit τ v).toIneq :=
    sum_congr rfl fun v hv => by
      simp only [falseLit, τ', Function.update_of_ne (ne_of_mem_of_not_mem hv hx)]
  have hx' : (falseLit τ x).toIneq + (falseLit τ' x).toIneq = -contra := by
    rw [← nonneg_add_leOne x]
    cases hτ : τ x <;> simp [τ', falseLit, hτ, add_comm]
  obtain ⟨t, ht⟩ := h τ
  obtain ⟨t', ht'⟩ := h τ'
  rw [sum_insert hx, ← add_assoc, add_comm _ (falseLit τ x).toIneq, add_assoc] at ht
  rw [sum_insert hx, hT, ← add_assoc, add_comm _ (falseLit τ' x).toIneq, add_assoc] at ht'
  have hsum : (falseLit τ x).toIneq + L + ((falseLit τ' x).toIneq + L) = 2 • L - contra := by
    rw [two_nsmul, sub_eq_add_neg, ← hx']
    abel
  have hcoeff : (2 • L - contra).coeff = ((2 : ℕ) : ℤ) • L.coeff := by
    simp [two_smul]
  have := (ht.add ht').div 2 two_pos fun v => by rw [hsum, hcoeff]; exact ⟨_, rfl⟩
  rw [hsum, div_eq_of two_pos hcoeff (by simp; omega) (by simp)] at this
  exact ⟨_, this⟩

/-- **Eliminating the variables of `W`**: if `I + ∑_{v ∈ W} ℓᵥ` is derivable for every
assignment `τ`, where `ℓᵥ` is the literal on `v` false under `τ`, then `I` is derivable, by
merging siblings (`exists_derivableInSize_merge`) one variable at a time. -/
private theorem exists_derivableInSize_of_forall_falseLit {I : Ineq V} (W : Finset V)
    (hleaf : ∀ τ : V → Bool, ∃ t, DerivableInSize Γ (I + ∑ v ∈ W, (falseLit τ v).toIneq) t) :
    ∃ t, DerivableInSize Γ I t := by
  classical
  have key : ∀ U T : Finset V, (∀ τ : V → Bool,
      ∃ t, DerivableInSize Γ (I + ∑ v ∈ T ∪ U, (falseLit τ v).toIneq) t) →
      ∀ τ : V → Bool, ∃ t, DerivableInSize Γ (I + ∑ v ∈ T, (falseLit τ v).toIneq) t := by
    intro U
    induction U using Finset.induction_on with
    | empty => simp
    | @insert x U _ ih =>
      intro T h τ
      have h' := ih (insert x T) fun τ => by rw [insert_union, ← union_insert]; exact h τ
      by_cases hxT : x ∈ T
      · simpa [insert_eq_of_mem hxT] using h' τ
      · exact exists_derivableInSize_merge hxT h'
  simpa using key W ∅ (by simpa using hleaf) fun _ => false

/-! ### Completeness -/

/-- Refutation completeness for a finite system: at every assignment `τ` some inequality of `Γ`
fails, which gives the clause excluding `τ`, and eliminating the variables of `Γ` leaves
`0 ≥ 1`. -/
private theorem exists_refutableInSize_of_finite (hΓ : Γ.Finite)
    (h : ¬ ∃ σ : V → Bool, ∀ I ∈ Γ, I.Holds σ) : ∃ s, RefutableInSize Γ s := by
  classical
  set S : Finset V := hΓ.toFinset.biUnion fun I => I.coeff.support
  refine exists_derivableInSize_of_forall_falseLit S fun τ => ?_
  obtain ⟨I, hI, hIτ⟩ : ∃ I ∈ Γ, ¬ I.Holds τ := by
    by_contra hne
    exact h ⟨τ, fun I hI => not_not.1 fun hn => hne ⟨I, hI, hn⟩⟩
  have hsub : I.coeff.support ⊆ S :=
    subset_biUnion_of_mem (fun I : Ineq V => I.coeff.support) (hΓ.mem_toFinset.2 hI)
  exact ⟨_, derivableInSize_excl hsub hIτ (.hyp hI)⟩

/-- The 0/1 solutions of an inequality form a closed set of assignments. -/
private theorem isClosed_setOf_holds (I : Ineq V) : IsClosed {σ : V → Bool | I.Holds σ} := by
  have : Continuous fun σ : V → Bool => I.lhs σ := by
    simp only [lhs_eq_finsuppSum, Finsupp.sum]
    exact continuous_finsetSum _ fun v _ =>
      (continuous_of_discreteTopology (f := fun b : Bool => I.coeff v * b.toInt)).comp
        (continuous_apply v)
  exact isClosed_le continuous_const this

/-- **Refutation completeness of cutting planes**: every system of integer linear inequalities
with no 0/1 solution has a cutting planes refutation. The system may be infinite: by compactness
a finite subsystem has no 0/1 solution. -/
theorem exists_refutableInSize_of_not_exists_holds (h : ¬ ∃ σ : V → Bool, ∀ I ∈ Γ, I.Holds σ) :
    ∃ s, RefutableInSize Γ s := by
  classical
  obtain ⟨u, hu⟩ := isCompact_univ.elim_finite_subfamily_closed
    (fun I : Γ => {σ : V → Bool | I.1.Holds σ}) (fun I => isClosed_setOf_holds I.1)
    (Set.disjoint_left.2 fun σ _ hσ => h ⟨σ, fun I hI => Set.mem_iInter.1 hσ ⟨I, hI⟩⟩)
  have hfin : (↑(u.image Subtype.val) : Set (Ineq V)).Finite := (u.image Subtype.val).finite_toSet
  obtain ⟨s, ls, hls, hc, hlen⟩ := exists_refutableInSize_of_finite hfin fun ⟨σ, hσ⟩ => by
    refine Set.disjoint_left.1 hu (Set.mem_univ σ) (Set.mem_iInter₂.2 fun I hI => ?_)
    exact hσ I.1 (mem_coe.2 (mem_image_of_mem _ hI))
  refine ⟨s, ls, hls.mono fun I hI => ?_, hc, hlen⟩
  obtain ⟨J, -, rfl⟩ := mem_image.1 (mem_coe.1 hI)
  exact J.2

/-- **Cutting planes refute exactly the systems with no 0/1 solution.** -/
theorem exists_refutableInSize_iff_not_exists_holds :
    (∃ s, RefutableInSize Γ s) ↔ ¬ ∃ σ : V → Bool, ∀ I ∈ Γ, I.Holds σ :=
  ⟨fun ⟨_, h⟩ => h.not_exists_holds, exists_refutableInSize_of_not_exists_holds⟩

/-! ### Implicational completeness -/

/-- The left-hand side depends only on the coefficients. -/
private theorem lhs_congr {I J : Ineq V} (h : I.coeff = J.coeff) (σ : V → Bool) :
    I.lhs σ = J.lhs σ := by
  rw [lhs_eq_finsuppSum, lhs_eq_finsuppSum, h]

/-- The line `A + ∑_{v ∈ S} ℓᵥ ≥ c + 1` at a leaf `τ` of the decision tree on `S`, when
`A(τ) > c`: adding `(d + aᵥ eᵥ) • (ℓᵥ ≥ 0)` for `v ∈ S` to `(d - 1) • (A ≥ c)` gives the
coefficients of `d • (A + ∑_{v ∈ S} ℓᵥ)`, and rounded division by `d` gives the line. -/
private theorem exists_derivableInSize_leaf {A : V →₀ ℤ} {c : ℤ} {S : Finset V}
    (hS : A.support ⊆ S) {τ : V → Bool} (hτ : c < (⟨A, c⟩ : Ineq V).lhs τ) {s : ℕ}
    (hI : DerivableInSize Γ ⟨A, c⟩ s) :
    ∃ t, DerivableInSize Γ (⟨A, c + 1⟩ + ∑ v ∈ S, (falseLit τ v).toIneq) t := by
  classical
  set I : Ineq V := ⟨A, c⟩
  set X : ℤ := I.lhs τ
  set B : ℤ := ∑ v ∈ S, |A v|
  set d : ℕ := (B + (X - c) + 1).toNat
  have hB : 0 ≤ B := sum_nonneg fun v _ => abs_nonneg _
  have hd : (d : ℤ) = B + (X - c) + 1 := Int.toNat_of_nonneg (by omega)
  have hd2 : 2 ≤ d := by omega
  have hd1 : ((d - 1 : ℕ) : ℤ) = d - 1 := by push_cast [Nat.cast_sub (by omega : 1 ≤ d)]; ring
  have hle : ∀ v ∈ S, -(A v * sgn τ v) ≤ B := fun v hv => by
    refine le_trans ?_ (single_le_sum (f := fun v => |A v|) (fun _ _ => abs_nonneg _) hv)
    cases h : τ v <;> simp [sgn, h, le_abs_self, neg_le_abs]
  set k : V → ℕ := fun v => ((d : ℤ) + A v * sgn τ v).toNat
  have hk : ∀ v ∈ S, (k v : ℤ) = d + A v * sgn τ v := fun v hv =>
    Int.toNat_of_nonneg (by have := hle v hv; omega)
  have hk0 : ∀ v ∈ S, 0 < k v := fun v hv => by have := hle v hv; have := hk v hv; omega
  set K : Ineq V := ⟨A, c + 1⟩ + ∑ v ∈ S, (falseLit τ v).toIneq
  set J : Ineq V := (d - 1) • I + ∑ v ∈ S, k v • (falseLit τ v).toIneq
  have hJ : DerivableInSize Γ J (s + 1 + #S * (2 + 1)) :=
    (hI.smul (d - 1) (by omega)).add_sum S fun v hv => (DerivableInSize.literal _).smul _ (hk0 v hv)
  have hcoeff : J.coeff = (d : ℤ) • K.coeff := by
    ext w
    simp only [J, K, I, coeff_add, coeff_sum, coeff_nsmul, coeff_falseLit,
      Finsupp.add_apply, Finset.sum_apply', Finsupp.smul_apply, Finsupp.single_apply,
      smul_eq_mul, Finsupp.smul_single, sum_ite_eq', nsmul_eq_mul]
    by_cases hw : w ∈ S
    · simp only [hw, ite_true]
      rw [hd1]
      linear_combination (A w) * sgn_mul_self τ w + sgn τ w * hk w hw
    · have : A w = 0 := Finsupp.notMem_support_iff.1 fun h => hw (hS h)
      simp [hw, this]
  have hlhsK : K.lhs τ = X + ∑ v ∈ S, (falseLit τ v).toIneq.bound := by
    have hX : (⟨A, c + 1⟩ : Ineq V).lhs τ = X := lhs_congr (I := ⟨A, c + 1⟩) (J := I) rfl τ
    simp only [K, lhs_add, lhs_sum, lhs_falseLit, hX]
  have hlhsJ : J.lhs τ = (d - 1 : ℕ) * X + ∑ v ∈ S, (k v : ℤ) * (falseLit τ v).toIneq.bound := by
    simp only [J, X, lhs_add, lhs_sum, lhs_nsmul, lhs_falseLit]
  have hboundJ : J.bound = (d - 1 : ℕ) * c + ∑ v ∈ S, (k v : ℤ) * (falseLit τ v).toIneq.bound := by
    simp only [J, I, bound_add, bound_sum, bound_nsmul, nsmul_eq_mul]
  have hboundK : K.bound = c + 1 + ∑ v ∈ S, (falseLit τ v).toIneq.bound := by
    simp only [K, bound_add, bound_sum]
  have hJK : J.lhs τ = d * K.lhs τ := lhs_of_coeff_eq_smul τ hcoeff
  have hdiv : J.div d = K := by
    refine div_eq_of (by omega) hcoeff ?_ ?_ <;> rw [hd1] at hlhsJ hboundJ <;> nlinarith
  have := hJ.div d (by omega) fun v => by rw [hcoeff]; exact ⟨_, rfl⟩
  rw [hdiv] at this
  exact ⟨_, this⟩

/-- **The inductive step** `A ≥ c ⟹ A ≥ c + 1` for `c` below every value of `A` at the 0/1
solutions of a finite `Γ₀ ⊆ Γ`, by the decision tree over the variables `W` of `Γ₀` and `A`. -/
private theorem exists_derivableInSize_succ {Γ₀ : Finset (Ineq V)} (hΓ₀ : ↑Γ₀ ⊆ Γ)
    {A : V →₀ ℤ} {c : ℤ}
    (himp : ∀ τ : V → Bool, (∀ J ∈ Γ₀, J.Holds τ) → c < (⟨A, c⟩ : Ineq V).lhs τ) {s : ℕ}
    (hI : DerivableInSize Γ ⟨A, c⟩ s) : ∃ t, DerivableInSize Γ ⟨A, c + 1⟩ t := by
  classical
  set W : Finset V := A.support ∪ Γ₀.biUnion fun J => J.coeff.support
  have hleaf (τ : V → Bool) :
      ∃ t, DerivableInSize Γ (⟨A, c + 1⟩ + ∑ v ∈ W, (falseLit τ v).toIneq) t := by
    by_cases hτ : ∃ J ∈ Γ₀, ¬ J.Holds τ
    · obtain ⟨J, hJ, hJτ⟩ := hτ
      have hsub : J.coeff.support ⊆ W :=
        subset_union_right.trans' (subset_biUnion_of_mem (fun J : Ineq V => J.coeff.support) hJ)
      have := hI.add (derivableInSize_excl hsub hJτ (.hyp (hΓ₀ hJ)))
      have e : (⟨A, c⟩ : Ineq V) + (contra + ∑ v ∈ W, (falseLit τ v).toIneq) =
          ⟨A, c + 1⟩ + ∑ v ∈ W, (falseLit τ v).toIneq := by
        ext <;> simp [add_assoc]
      rw [e] at this
      exact ⟨_, this⟩
    · push Not at hτ
      exact exists_derivableInSize_leaf subset_union_left (himp τ hτ) hI
  exact exists_derivableInSize_of_forall_falseLit W hleaf

/-- **Implicational completeness of cutting planes**: over a nonempty type of variables, every
inequality satisfied by all 0/1 solutions of `Γ` is derivable from `Γ`. -/
theorem exists_derivableInSize_of_forall_holds [Nonempty V] {I : Ineq V}
    (h : ∀ σ : V → Bool, (∀ J ∈ Γ, J.Holds σ) → I.Holds σ) : ∃ s, DerivableInSize Γ I s := by
  classical
  obtain ⟨v₀⟩ := ‹Nonempty V›
  -- Compactness: a refutation of `Γ` with `¬ I` uses finitely many hypotheses `Γ₀` of `Γ`.
  set N : Ineq V := ⟨-I.coeff, 1 - I.bound⟩
  have hN (σ : V → Bool) : N.Holds σ ↔ ¬ I.Holds σ := by
    have : N.lhs σ = -1 * I.lhs σ := lhs_of_coeff_eq_smul σ (by simp [N])
    have hb : N.bound = 1 - I.bound := rfl
    simp only [Holds, this, hb]
    omega
  obtain ⟨-, ls, hls, hc, -⟩ := exists_refutableInSize_of_not_exists_holds
    (Γ := insert N Γ) fun ⟨σ, hσ⟩ => (hN σ).1 (hσ N (Set.mem_insert _ _))
      (h σ fun J hJ => hσ J (Set.mem_insert_of_mem _ hJ))
  set Γ₀ : Finset (Ineq V) := ls.toFinset.filter (· ∈ Γ)
  have hΓ₀ : ↑Γ₀ ⊆ Γ := fun J hJ => (mem_filter.1 hJ).2
  have himp (σ : V → Bool) (hσ : ∀ J ∈ Γ₀, J.Holds σ) : I.Holds σ := by
    by_contra hI
    refine not_holds_contra σ (hls.restrict.holds (fun J ⟨hJ, hJls⟩ => ?_) hc)
    rcases Set.mem_insert_iff.1 hJ with rfl | hJ
    · exact (hN σ).2 hI
    · exact hσ J (mem_filter.2 ⟨List.mem_toFinset.2 hJls, hJ⟩)
  -- Bound lowering: `0 ≥ -1` is `x ≥ 0` plus `-x ≥ -1`.
  have hlow {c b : ℤ} (hbc : b ≤ c) (hc : ∃ s, DerivableInSize Γ ⟨I.coeff, c⟩ s) :
      ∃ s, DerivableInSize Γ ⟨I.coeff, b⟩ s := by
    obtain ⟨s, hs⟩ := hc
    obtain rfl | hlt := hbc.eq_or_lt
    · exact ⟨s, hs⟩
    have := hs.add (((DerivableInSize.nonneg v₀).add (.leOne v₀)).smul (c - b).toNat (by omega))
    have e : (⟨I.coeff, c⟩ : Ineq V) + (c - b).toNat • (nonneg v₀ + leOne v₀) = ⟨I.coeff, b⟩ := by
      ext <;> simp [nonneg_add_leOne]
      omega
    rw [e] at this
    exact ⟨_, this⟩
  -- The base `A ≥ c₀`, a sum of multiples of literal axioms.
  set τ₀ : V → Bool := fun v => decide (I.coeff v < 0)
  set J₀ : Ineq V := (nonneg v₀ + leOne v₀) +
    ∑ v ∈ I.coeff.support, (|I.coeff v|).toNat • (falseLit τ₀ v).toIneq
  have hJ₀ : ∃ s, DerivableInSize Γ ⟨I.coeff, J₀.bound⟩ s := by
    have := ((DerivableInSize.nonneg v₀).add (.leOne v₀)).add_sum I.coeff.support
      fun v hv => (DerivableInSize.literal (Γ := Γ) (falseLit τ₀ v)).smul (|I.coeff v|).toNat
        (by simpa [Int.lt_toNat] using abs_pos.2 (Finsupp.mem_support_iff.1 hv))
    change DerivableInSize Γ J₀ _ at this
    have hterm (v : V) : |I.coeff v| * sgn τ₀ v = I.coeff v := by
      rcases lt_or_ge (I.coeff v) 0 with h | h
      · simp [sgn, τ₀, h, abs_of_neg h]
      · simp [sgn, τ₀, h.not_gt, abs_of_nonneg h]
    have e : J₀ = ⟨I.coeff, J₀.bound⟩ := by
      refine Ineq.ext ?_ rfl
      simp only [J₀, coeff_add, coeff_sum, coeff_nsmul, coeff_falseLit, nonneg_add_leOne,
        coeff_neg, coeff_contra, neg_zero, zero_add, Finsupp.smul_single, nsmul_eq_mul,
        Int.toNat_of_nonneg (abs_nonneg _), hterm]
      exact Finsupp.sum_single I.coeff
    rw [e] at this
    exact ⟨_, this⟩
  -- Iterate the step from `min c₀ b` up to `b`.
  set c₀ : ℤ := min J₀.bound I.bound
  have hstep : ∀ n : ℕ, c₀ + n ≤ I.bound → ∃ s, DerivableInSize Γ ⟨I.coeff, c₀ + n⟩ s := by
    intro n
    induction n with
    | zero => exact fun _ => by simpa using hlow (b := c₀) (min_le_left _ _) hJ₀
    | succ n ih =>
      intro hn
      obtain ⟨s, hs⟩ := ih (by omega)
      have := exists_derivableInSize_succ hΓ₀ (fun τ hτ => by
        have := himp τ hτ
        simp only [Holds] at this
        have := lhs_congr (I := ⟨I.coeff, c₀ + n⟩) (J := I) rfl τ
        omega) hs
      simpa [add_assoc] using this
  obtain ⟨s, hs⟩ := hstep (I.bound - c₀).toNat (by omega)
  have e : (⟨I.coeff, c₀ + (I.bound - c₀).toNat⟩ : Ineq V) = I := by
    ext <;> simp
    omega
  rw [e] at hs
  exact ⟨s, hs⟩

/-- **Cutting planes derive exactly the implied inequalities**: over a nonempty type of variables,
`I` is derivable from `Γ` iff every 0/1 solution of `Γ` satisfies `I`. Over an empty type of
variables the forward direction holds but not the converse: `0 ≥ 0` is implied by the empty
system, which derives nothing. -/
theorem exists_derivableInSize_iff_forall_holds [Nonempty V] {I : Ineq V} :
    (∃ s, DerivableInSize Γ I s) ↔ ∀ σ : V → Bool, (∀ J ∈ Γ, J.Holds σ) → I.Holds σ :=
  ⟨fun ⟨_, h⟩ _ hσ => h.holds hσ, exists_derivableInSize_of_forall_holds⟩

end Cslib.Logic.PL.CuttingPlanes
