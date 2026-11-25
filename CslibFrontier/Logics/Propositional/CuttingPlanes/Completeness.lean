/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CuttingPlanes
import CslibFrontier.Logics.Propositional.CuttingPlanes.Resolution
import Mathlib.Tactic.LinearCombination
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Instances.Int
import Mathlib.Topology.Order.OrderClosed

/-!
# Refutation completeness of cutting planes

Every system `Γ` of integer linear inequalities (`Cslib.Logic.PL.Ineq`) without a 0/1 solution has
a cutting planes refutation
(`Cslib.Logic.PL.CuttingPlanes.exists_refutableInSize_of_not_exists_holds`). With soundness, `Γ` is
refutable iff it has no 0/1 solution
(`Cslib.Logic.PL.CuttingPlanes.exists_refutableInSize_iff_not_exists_holds`). The system may be
infinite and over any type of variables; the refutations may be exponentially long.

The proof follows the route of [Cook, Coullard and Turán][CookCoullardTuran1987]: reduce to
clauses, then use completeness of resolution.

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
3. **Resolution.** The `2^|S|` clauses excluding the assignments of `S` form an unsatisfiable CNF,
   which cutting planes refute
   (`Cslib.Logic.PL.CuttingPlanes.exists_refutableInSize_iff_not_satisfiable`). Replaying that
   refutation on top of the derivations of its clauses
   (`Cslib.Logic.PL.CuttingPlanes.DerivableInSize.extend`) refutes `Γ`.

Implicational completeness, that every inequality implied by `Γ` is derivable from it, is not
proved here.

## Main results

* `Cslib.Logic.PL.CuttingPlanes.exists_refutableInSize_of_not_exists_holds`: refutation
  completeness.
* `Cslib.Logic.PL.CuttingPlanes.exists_refutableInSize_iff_not_exists_holds`: a system is
  refutable iff it has no 0/1 solution.

## References

* [W. Cook, C. R. Coullard, Gy. Turán, *On the complexity of cutting-plane
  proofs*][CookCoullardTuran1987]
-/

public section

namespace Cslib.Logic.PL.CuttingPlanes

open Finset Ineq

variable {V : Type*} {Γ : Set (Ineq V)}

/-! ### Composing derivations -/

/-- Derivations of the inequalities of a list combine into one proof containing all of them. -/
private theorem exists_isProof_forall_mem {L : List (Ineq V)}
    (h : ∀ J ∈ L, ∃ s, DerivableInSize Γ J s) : ∃ ls, IsProof Γ ls ∧ ∀ J ∈ L, J ∈ ls := by
  induction L with
  | nil => exact ⟨[], .nil, by simp⟩
  | cons J L ih =>
    obtain ⟨ls, hls, hmem⟩ := ih fun K hK => h K (List.mem_cons_of_mem _ hK)
    obtain ⟨s, ls', hls', hJ, -⟩ := h J List.mem_cons_self
    refine ⟨ls' ++ ls, hls'.append hls, fun K hK => ?_⟩
    rcases List.mem_cons.1 hK with rfl | hK
    · exact List.mem_append_left _ hJ
    · exact List.mem_append_right _ (hmem K hK)

/-- A derivation from inequalities, each of which is derivable from `Γ`, gives a derivation from
`Γ`. -/
private theorem exists_derivableInSize_of_forall {Δ : Set (Ineq V)} {L : List (Ineq V)}
    (hΔ : ∀ J ∈ Δ, J ∈ L) (hL : ∀ J ∈ L, ∃ s, DerivableInSize Γ J s) {I : Ineq V} {t : ℕ}
    (hI : DerivableInSize Δ I t) : ∃ s, DerivableInSize Γ I s := by
  obtain ⟨ls, hls, hmem⟩ := exists_isProof_forall_mem hL
  obtain ⟨ls'', h'', hI', -⟩ := hI.extend hls fun J hJ => Or.inr (hmem J (hΔ J hJ))
  exact ⟨_, ls'' ++ ls, h'', hI', le_rfl⟩

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

/-- The clause of the literals on `S` that are false under `σ`. -/
private noncomputable def exclClause (S : Finset V) (σ : V → Bool) : Clause V :=
  S.toList.map (falseLit σ)

private theorem toIneq_exclClause [DecidableEq V] (S : Finset V) (σ : V → Bool) :
    (exclClause S σ).toIneq = contra + ∑ v ∈ S, (falseLit σ v).toIneq := by
  have hinj : Function.Injective (falseLit σ) := fun v w h => congrArg Prod.fst h
  rw [exclClause, Clause.toIneq_of_nodup ((nodup_toList S).map hinj), List.map_map,
    Function.comp_def, sum_map_toList]

/-- The clause excluding `τ` fails under every assignment agreeing with `τ` on `S`. -/
private theorem eval_exclClause {S : Finset V} {σ τ : V → Bool}
    (h : ∀ v ∈ S, τ v = σ v) : (exclClause S τ).eval σ = false := by
  rw [Bool.eq_false_iff, ne_eq, Clause.eval_eq_true_iff]
  rintro ⟨l, hl, hσ⟩
  obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hl
  simp [falseLit, ← h v (mem_toList.1 hv)] at hσ

/-! ### Completeness -/

/-- Refutation completeness for a finite system. -/
private theorem exists_refutableInSize_of_finite (hΓ : Γ.Finite)
    (h : ¬ ∃ σ : V → Bool, ∀ I ∈ Γ, I.Holds σ) : ∃ s, RefutableInSize Γ s := by
  classical
  set S : Finset V := hΓ.toFinset.biUnion fun I => I.coeff.support
  let ext (ρ : S → Bool) (v : V) : Bool := if hv : v ∈ S then ρ ⟨v, hv⟩ else false
  let φ : CNF V := (univ : Finset (S → Bool)).toList.map fun ρ => exclClause S (ext ρ)
  have hφ : ¬ φ.Satisfiable := by
    rintro ⟨σ, hσ⟩
    have := (CNF.eval_eq_true_iff σ φ).1 hσ (exclClause S (ext fun v => σ v))
      (List.mem_map.2 ⟨fun v => σ v, mem_toList.2 (mem_univ _), rfl⟩)
    rw [eval_exclClause fun v hv => by simp [ext, hv]] at this
    exact Bool.false_ne_true this
  obtain ⟨t, ht⟩ := exists_refutableInSize_iff_not_satisfiable.2 hφ
  refine exists_derivableInSize_of_forall (L := φ.map Clause.toIneq) ?_ ?_ ht
  · rintro J ⟨c, hc, rfl⟩
    exact List.mem_map_of_mem hc
  · intro J hJ
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hJ
    obtain ⟨ρ, -, rfl⟩ := List.mem_map.1 hc
    obtain ⟨I, hI, hIσ⟩ : ∃ I ∈ Γ, ¬ I.Holds (ext ρ) := by
      by_contra hne
      exact h ⟨ext ρ, fun I hI => not_not.1 fun hn => hne ⟨I, hI, hn⟩⟩
    have hsub : I.coeff.support ⊆ S :=
      subset_biUnion_of_mem (fun I : Ineq V => I.coeff.support) (hΓ.mem_toFinset.2 hI)
    rw [toIneq_exclClause]
    exact ⟨_, derivableInSize_excl hsub hIσ (.hyp hI)⟩

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

end Cslib.Logic.PL.CuttingPlanes
