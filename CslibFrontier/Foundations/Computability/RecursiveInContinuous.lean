/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Computability.RecursiveInJoin
public import CslibFrontier.Foundations.Computability.RecursiveInUniversal
public import Mathlib.Topology.MetricSpace.PiNat

/-!
# Continuity on Baire space as relative computability

A map `F : (ℕ → ℕ) → (ℕ → ℕ)` on Baire space, with the product topology of discrete `ℕ`, is
*computable relative to the oracle `p`* when one oracle code `c` computes every output entry from
the join of `p` with the input: `F x n = Φ_c^{p ⊕ x}(n)` for all `x` and `n`. This file proves
that the total maps computable relative to some oracle are exactly the continuous ones
(`Nat.RecursiveIn.Code.continuous_iff_exists_code`).

* *Computable implies continuous* (`Nat.RecursiveIn.Code.continuous_of_eval`). By the use
  principle (`Nat.RecursiveIn.Code.exists_use`), a convergent computation relative to `p ⊕ x`
  reads only finitely many entries of `x`, so each output entry is constant on a cylinder.
* *Continuous implies computable, through one fixed code*
  (`Nat.RecursiveIn.Code.exists_code_continuous`). A single code `e` serves every continuous `F`:
  the oracle `p_F` answers a query `⟨n, σ⟩` by `v + 1` when every input extending the finite
  sequence `σ` has `n`-th output `v`, and by `0` otherwise. The code searches for the least `k`
  such that `p_F` answers the prefix of length `k` of the input with a nonzero value. By
  continuity the search terminates.

## Main results

* `Partrec.join_coe`: the join of two total functions is total.
* `Nat.RecursiveIn.Code.continuous_iff_forall_exists_cylinder`: continuity on Baire space as
  dependence of each output entry on a finite prefix of the input.
* `Nat.RecursiveIn.Code.exists_code_continuous`: one code computes every continuous map relative
  to an oracle that encodes the map.
* `Nat.RecursiveIn.Code.continuous_of_eval`: a total map computable relative to an oracle is
  continuous.
* `Nat.RecursiveIn.Code.continuous_iff_exists_code`: the continuity theorem.

## Implementation notes

The statements take a total map with values in `ℕ → ℕ` in curried form, `(ℕ → ℕ) → ℕ → ℕ`, and
compare it with code evaluation entry by entry. Partial maps, closure under composition and the
notion of a stream function computable relative to an oracle as a definition (the first milestone
of the type-2 computability issue #6830) are not developed here.

## References

* [K. Weihrauch, *Computable Analysis: An Introduction*][Weihrauch2000], Chapters 2 and 3
  (type-2 machines and the continuity of computable functions; the precise locators are to be
  checked).
* [J. van Oosten, *Realizability: An Introduction to its Categorical Side*][vanOosten2008], §1.4
  (Kleene's second model, whose elements code continuous functionals; to be checked).
-/

public section

open Encodable Denumerable PiNat
open scoped Partrec

/-- The join of two total functions is total. -/
theorem Partrec.join_coe (f g : ℕ → ℕ) :
    ((f : ℕ →. ℕ) ⊕ (g : ℕ →. ℕ)) =
      ((fun n => cond n.bodd (2 * g n.div2 + 1) (2 * f n.div2) : ℕ → ℕ) : ℕ →. ℕ) := by
  funext n
  cases h : n.bodd <;> simp [Partrec.join, h]

namespace Nat.RecursiveIn.Code

/-- A map on Baire space is continuous if and only if each output entry depends only on a finite
prefix of the input. -/
theorem continuous_iff_forall_exists_cylinder {F : (ℕ → ℕ) → ℕ → ℕ} :
    Continuous F ↔ ∀ x n, ∃ k, ∀ y ∈ cylinder x k, F y n = F x n := by
  refine ⟨fun hF x n => ?_, fun h => continuous_pi_iff.2 fun n =>
    continuous_discrete_rng.2 fun v => isOpen_iff_forall_mem_open.2 fun x hx => ?_⟩
  · have ho : IsOpen ((fun y => F y n) ⁻¹' {F x n}) :=
      (isOpen_discrete _).preimage (continuous_pi_iff.1 hF n)
    obtain ⟨_, ⟨z, k, rfl⟩, hx, hsub⟩ := (isTopologicalBasis_cylinders fun _ : ℕ => ℕ)
      |>.exists_subset_of_mem_open (Set.mem_preimage.2 rfl) ho
    exact ⟨k, fun y hy => hsub (by rwa [← mem_cylinder_iff_eq.1 hx])⟩
  · obtain ⟨k, hk⟩ := h x n
    exact ⟨cylinder x k, fun y hy => (hk y hy).trans hx, isOpen_cylinder (fun _ : ℕ => ℕ) x k,
      self_mem_cylinder x k⟩

/-- Two inputs have the same prefix of length `k` exactly when one lies in the cylinder of length
`k` around the other. -/
private theorem prefixOf_eq_iff {x y : ℕ → ℕ} {k : ℕ} :
    prefixOf y k = prefixOf x k ↔ y ∈ cylinder x k := by
  refine ⟨fun h i hi => ?_, fun h => List.map_congr_left fun i hi => h i (List.mem_range.1 hi)⟩
  simpa [prefixOf, hi] using congrArg (·[i]?) h

/-- The answer of the oracle encoding `F` at `⟨n, σ⟩`: `v + 1` when every input whose prefix is
`σ` has `n`-th output `v`, and `0` if there is no such `v`. -/
private noncomputable def nbhd (F : (ℕ → ℕ) → ℕ → ℕ) (n : ℕ) (σ : List ℕ) : ℕ :=
  open Classical in
  if h : ∃ v, ∀ y : ℕ → ℕ, prefixOf y σ.length = σ → F y n = v then h.choose + 1 else 0

/-- A nonzero answer of `nbhd F` on a prefix of `x` is `F x n + 1`. -/
private theorem nbhd_eq {F : (ℕ → ℕ) → ℕ → ℕ} {x : ℕ → ℕ} {n k : ℕ}
    (h : nbhd F n (prefixOf x k) ≠ 0) : nbhd F n (prefixOf x k) = F x n + 1 := by
  unfold nbhd at h ⊢
  split_ifs at h ⊢ with hv
  · rw [hv.choose_spec x (by rw [length_prefixOf])]
  · exact absurd rfl h

/-- `nbhd F` answers a prefix of `x` on which the `n`-th output is constant with a nonzero
value. -/
private theorem nbhd_ne_zero {F : (ℕ → ℕ) → ℕ → ℕ} {x : ℕ → ℕ} {n k : ℕ}
    (hk : ∀ y ∈ cylinder x k, F y n = F x n) : nbhd F n (prefixOf x k) ≠ 0 := by
  unfold nbhd
  split_ifs with hv
  · exact Nat.succ_ne_zero _
  · exact absurd ⟨F x n, fun y hy => hk y (prefixOf_eq_iff.1 (by rwa [length_prefixOf] at hy))⟩ hv

/-- Pairs of an oracle and an input, joined. -/
private abbrev joined : (ℕ → ℕ) × (ℕ → ℕ) → ℕ →. ℕ := fun i => (i.1 : ℕ →. ℕ) ⊕ (i.2 : ℕ →. ℕ)

/-- One code reads the oracle at `⟨n, encode (prefixOf x k)⟩` on input `⟨n, k⟩`, relative to the
join of the oracle with the input `x`. -/
private theorem hasUniformCode_query :
    HasUniformCode joined fun i m =>
      Part.some (i.1 (Nat.pair m.unpair.1 (encode (prefixOf i.2 m.unpair.2)))) := by
  have hp : HasUniformCode joined fun i => (i.1 : ℕ →. ℕ) := ⟨joinLeft, fun _ => eval_joinLeft ..⟩
  obtain ⟨c, hc⟩ := hasUniformCode_prefixOf
  have hpre : HasUniformCode joined fun i k => Part.some (encode (prefixOf i.2 k)) :=
    ⟨c.subst joinRight, fun i => by rw [eval_subst, eval_joinRight, hc]⟩
  refine (hp.comp ((HasUniformCode.of_computable (Computable.fst.comp Computable.unpair)).pair
    (hpre.comp (HasUniformCode.of_computable (Computable.snd.comp Computable.unpair))))).of_eq
    fun i m => ?_
  have h : ∀ a, (Part.some a >>= (i.1 : ℕ →. ℕ)) = Part.some (i.1 a) := fun a => Part.bind_some a _
  simp [Seq.seq, h]

/-- One code computes, relative to `p ⊕ x`, the answer of `p` at the first prefix of `x` that it
answers with a nonzero value, minus one. -/
private theorem hasUniformCode_search :
    HasUniformCode joined fun i n =>
      (Nat.rfind fun k => Part.some (decide
        (1 - i.1 (Nat.pair n (encode (prefixOf i.2 k))) = 0))).map
        fun k => i.1 (Nat.pair n (encode (prefixOf i.2 k))) - 1 := by
  have hsub {f : ℕ → ℕ} (hf : Computable f) : HasUniformCode joined fun i m =>
      Part.some (f (i.1 (Nat.pair m.unpair.1 (encode (prefixOf i.2 m.unpair.2))))) :=
    ((HasUniformCode.of_computable hf).comp hasUniformCode_query).of_eq fun _ _ => by simp
  have htest := hsub
    (_root_.Primrec.nat_sub.comp (_root_.Primrec.const 1) _root_.Primrec.id).to_comp
  have hval := hsub
    (_root_.Primrec.nat_sub.comp _root_.Primrec.id (_root_.Primrec.const 1)).to_comp
  refine (hval.comp ((HasUniformCode.of_computable Computable.id).pair htest.rfind)).of_eq
    fun i n => ?_
  simp only [Seq.seq, Part.bind_eq_bind, Part.map_eq_map, Part.map_some, Part.bind_some,
    Nat.unpair_pair, id_eq, Part.bind_some_eq_map, Part.map_map, Function.comp_def]

/-- **Continuous maps are computable through one fixed code.** A single oracle code `e` computes
every continuous map `F` on Baire space relative to the join of an oracle `p` encoding `F` with
the input: `F x n = Φₑ^{p ⊕ x}(n)`. -/
theorem exists_code_continuous :
    ∃ e : Code, ∀ F : (ℕ → ℕ) → ℕ → ℕ, Continuous F → ∃ p : ℕ → ℕ, ∀ (x : ℕ → ℕ) n,
      eval ((p : ℕ →. ℕ) ⊕ (x : ℕ →. ℕ)) e n = Part.some (F x n) := by
  obtain ⟨e, he⟩ := hasUniformCode_search
  refine ⟨e, fun F hF => ⟨fun m => nbhd F m.unpair.1 (ofNat (List ℕ) m.unpair.2), fun x n => ?_⟩⟩
  rw [he (_, x)]
  simp only [Nat.unpair_pair, ofNat_encode]
  obtain ⟨k, hk⟩ := continuous_iff_forall_exists_cylinder.1 hF x n
  have hnz := nbhd_ne_zero hk
  have hdom : (Nat.rfind fun k => Part.some (decide (1 - nbhd F n (prefixOf x k) = 0))).Dom :=
    Nat.rfind_dom.2 ⟨k, Part.mem_some_iff.2 (decide_eq_true (by omega)).symm, fun _ => trivial⟩
  have hspec := of_decide_eq_true (Part.mem_some_iff.1 (Nat.rfind_spec (Part.get_mem hdom))).symm
  rw [← Part.some_get hdom, Part.map_some, nbhd_eq (by omega)]
  simp

/-- **Computable maps are continuous.** A total map on Baire space that one code computes
relative to the join of a fixed oracle `p` with the input is continuous. -/
theorem continuous_of_eval {F : (ℕ → ℕ) → ℕ → ℕ} {p : ℕ → ℕ} {c : Code}
    (h : ∀ (x : ℕ → ℕ) n, eval ((p : ℕ →. ℕ) ⊕ (x : ℕ →. ℕ)) c n = Part.some (F x n)) :
    Continuous F := by
  refine continuous_iff_forall_exists_cylinder.2 fun x n => ?_
  have hx := h x n
  rw [Partrec.join_coe] at hx
  obtain ⟨N, hN⟩ := exists_use (Part.eq_some_iff.1 hx)
  refine ⟨N, fun y hy => ?_⟩
  have hy' := h y n
  rw [Partrec.join_coe] at hy'
  refine Part.mem_unique (hy' ▸ Part.mem_some _) (hN _ fun i hi => ?_)
  have hdiv : i.div2 < N := lt_of_le_of_lt (by simp [Nat.div2_val, Nat.div_le_self]) hi
  cases i.bodd <;> simp [mem_cylinder_iff.1 hy _ hdiv]

/-- **The continuity theorem.** A total map on Baire space is continuous if and only if it is
computable relative to some oracle: some code computes it from the join of the oracle with the
input. -/
theorem continuous_iff_exists_code {F : (ℕ → ℕ) → ℕ → ℕ} :
    Continuous F ↔ ∃ (p : ℕ → ℕ) (c : Code), ∀ (x : ℕ → ℕ) n,
      eval ((p : ℕ →. ℕ) ⊕ (x : ℕ →. ℕ)) c n = Part.some (F x n) := by
  refine ⟨fun hF => ?_, fun ⟨_, _, h⟩ => continuous_of_eval h⟩
  obtain ⟨e, he⟩ := exists_code_continuous
  obtain ⟨p, hp⟩ := he F hF
  exact ⟨p, e, hp⟩

end Nat.RecursiveIn.Code
