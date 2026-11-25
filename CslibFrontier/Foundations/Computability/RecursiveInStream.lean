/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Computability.RecursiveInContinuous
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Type-2 computability on Baire space

A partial map `F : (ℕ → ℕ) →. (ℕ → ℕ)` on Baire space is *computable relative to the oracle `p`*
when one oracle code `c` computes every output entry from the join of `p` with the input:
`(F x) n = Φ_c^{p ⊕ x}(n)` for every `x` in the domain of `F` and every `n`
(`Nat.RecursiveIn.Code.ComputesStream`). Nothing is required outside the domain. A map is
*computable* when it is computable relative to the oracle that is constantly `0`, that is, relative
to no information (`Nat.RecursiveIn.StreamComputable`); equivalently, relative to some computable
oracle.

* *Composition.* If `c` computes `F` and `d` computes `G` relative to `p`, then the code
  `streamComp d c = d.subst (join joinLeft c)` computes `G ∘ F` relative to `p`: it runs `d`
  relative to `p ⊕ y`, where `y` is the output of `c` relative to `p ⊕ x`. The map
  `(d, c) ↦ streamComp d c` is primitive recursive. Maps computable relative to `p` and to `q`
  compose to a map computable relative to `p ⊕ q`.
* *Continuity.* By the use principle (`Nat.RecursiveIn.Code.exists_cylinder_of_mem_eval_join`), a
  map computable relative to a total oracle is continuous on its domain. Its code computes it on
  the set of inputs on which the code converges at every entry, a Gδ set that contains the domain.
  For total maps, the continuity theorem `Nat.RecursiveIn.Code.continuous_iff_exists_code` becomes
  `Continuous F ↔ ∃ p, StreamComputableIn p F`.
* *The effective form.* A total map is computable exactly when it has a computable associate
  (`Nat.RecursiveIn.Code.IsAssociate`). One direction runs the fixed search code of
  `Nat.RecursiveIn.Code.exists_code_isAssociate` relative to the associate; for the other, the
  associate answers `⟨n, σ⟩` with `v + 1` when the stage-`|σ|` evaluation of the code against the
  finite oracle prefix `σ` returns `v`.

## Main definitions

* `Nat.RecursiveIn.Code.ComputesStream`: a code computes a partial map relative to an oracle.
* `Nat.RecursiveIn.Code.evalStream`: the partial map that a code computes relative to an oracle.
* `Nat.RecursiveIn.Code.streamComp`: the code of a composite.
* `Nat.RecursiveIn.StreamComputableIn`, `Nat.RecursiveIn.StreamComputable`: computability of a
  partial map relative to an oracle, and without one.

## Main results

* `Nat.RecursiveIn.Code.ComputesStream.comp`, `Nat.RecursiveIn.Code.primrec₂_streamComp`,
  `Nat.RecursiveIn.StreamComputableIn.comp`, `Nat.RecursiveIn.StreamComputable.comp`: closure
  under composition, with the composite's code a primitive recursive function of the two codes.
* `Nat.RecursiveIn.StreamComputableIn.of_turingReducible`: computability relative to `p` passes to
  every oracle that computes `p`.
* `Nat.RecursiveIn.streamComputable_iff_exists_computable`: computability without an oracle is
  computability relative to a computable oracle.
* `Nat.RecursiveIn.StreamComputableIn.continuous_get`: a map computable relative to a total oracle
  is continuous on its domain.
* `Nat.RecursiveIn.Code.isGδ_dom_evalStream`: the domain of `evalStream` is a Gδ set.
* `Nat.RecursiveIn.continuous_iff_streamComputableIn`: the continuity theorem for total maps.
* `Nat.RecursiveIn.streamComputable_iff_exists_isAssociate`: a total map is computable exactly when
  it has a computable associate.

## Implementation notes

Oracles are partial functions `ℕ →. ℕ`, as in `Nat.RecursiveIn.Code.eval`, so that the oracles
of a composite are joined by `Partrec.join`. The continuity results take a total oracle, since the
use principle `Nat.RecursiveIn.Code.exists_use` is stated for total oracles. A total map
`F : (ℕ → ℕ) → ℕ → ℕ` enters through the coercion to `(ℕ → ℕ) →. (ℕ → ℕ)`, and
`Nat.RecursiveIn.Code.computesStream_coe_iff` turns `ComputesStream` into the entrywise equations
of `RecursiveInContinuous`.

The definition is the relative form of the type-2 machines of Weihrauch: a code reads its input
through the oracle and produces its output entry by entry, instead of writing an infinite output
tape. The associate is Kleene's neighbourhood function in a form that only asks for consistency on
prefixes of each input, not monotonicity in the prefix.

## References

* [K. Weihrauch, *Computable Analysis: An Introduction*][Weihrauch2000], Chapters 2 and 3
  (type-2 machines, composition, the continuity of computable functions and their domains; the
  precise locators are to be checked).
* [S. C. Kleene and R. E. Vesley, *The Foundations of Intuitionistic Mathematics*][KleeneVesley1965]
  (neighbourhood functions and associates; the locator is to be checked).
* [J. van Oosten, *Realizability: An Introduction to its Categorical Side*][vanOosten2008], §1.4
  (Kleene's second model and its computable submodel; to be checked).
-/

public section

open Encodable Denumerable PiNat
open scoped Partrec Computability

namespace Nat.RecursiveIn

namespace Code

/-- The code `c` *computes the partial map `F`* on Baire space *relative to the oracle `p`*: for
every input `x` in the domain of `F`, the code run relative to the join `p ⊕ x` computes the output
`F x` entry by entry. Outside the domain of `F` nothing is required. -/
@[expose] def ComputesStream (p : ℕ →. ℕ) (c : Code) (F : (ℕ → ℕ) →. (ℕ → ℕ)) : Prop :=
  ∀ x, ∀ y ∈ F x, eval (p ⊕ (x : ℕ →. ℕ)) c = (y : ℕ →. ℕ)

/-- The partial map on Baire space that the code `c` computes relative to the oracle `p`: it is
defined at `x` when the code converges relative to `p ⊕ x` at every entry. -/
def evalStream (p : ℕ →. ℕ) (c : Code) : (ℕ → ℕ) →. (ℕ → ℕ) := fun x =>
  ⟨∀ n, (eval (p ⊕ (x : ℕ →. ℕ)) c n).Dom, fun h n => (eval (p ⊕ (x : ℕ →. ℕ)) c n).get (h n)⟩

@[simp]
theorem dom_evalStream {p : ℕ →. ℕ} {c : Code} {x : ℕ → ℕ} :
    (evalStream p c x).Dom ↔ ∀ n, (eval (p ⊕ (x : ℕ →. ℕ)) c n).Dom :=
  Iff.rfl

theorem mem_evalStream {p : ℕ →. ℕ} {c : Code} {x y : ℕ → ℕ} :
    y ∈ evalStream p c x ↔ eval (p ⊕ (x : ℕ →. ℕ)) c = (y : ℕ →. ℕ) := by
  refine ⟨fun ⟨h, hy⟩ => funext fun n => ?_, fun h => ⟨fun n => ?_, funext fun n => ?_⟩⟩
  · subst hy
    exact (Part.some_get (h n)).symm
  · exact (h ▸ Part.mem_some (y n) : y n ∈ eval (p ⊕ (x : ℕ →. ℕ)) c n).fst
  · exact Part.get_eq_of_mem (h ▸ Part.mem_some (y n)) _

/-- A code computes the partial map it evaluates to. -/
theorem computesStream_evalStream (p : ℕ →. ℕ) (c : Code) :
    ComputesStream p c (evalStream p c) :=
  fun _ _ => mem_evalStream.1

/-- A code computing `F` converges at every entry on the domain of `F`, so `F` is a restriction
of `evalStream p c`. -/
theorem ComputesStream.mem_evalStream {p : ℕ →. ℕ} {c : Code} {F : (ℕ → ℕ) →. (ℕ → ℕ)}
    (h : ComputesStream p c F) {x y : ℕ → ℕ} (hy : y ∈ F x) : y ∈ evalStream p c x :=
  Code.mem_evalStream.2 (h x y hy)

/-- For a total map, `ComputesStream` is the entrywise equation of `RecursiveInContinuous`. -/
theorem computesStream_coe_iff {p : ℕ →. ℕ} {c : Code} {F : (ℕ → ℕ) → ℕ → ℕ} :
    ComputesStream p c F ↔ ∀ (x : ℕ → ℕ) n, eval (p ⊕ (x : ℕ →. ℕ)) c n = Part.some (F x n) := by
  simp only [ComputesStream, PFun.coe_val, Part.mem_some_iff, forall_eq]
  exact forall_congr' fun x => funext_iff

/-! ### Composition -/

/-- The code of the composite of two maps computed relative to the same oracle `p`: it runs `d`
relative to `p ⊕ y`, where `y` is the output of `c` relative to `p ⊕ x`. -/
noncomputable def streamComp (d c : Code) : Code :=
  d.subst (join joinLeft c)

/-- The code of the composite is a primitive recursive function of the two codes. -/
theorem primrec₂_streamComp : Primrec₂ streamComp :=
  primrec₂_subst.comp Primrec.fst (primrec₂_join.comp (Primrec.const _) Primrec.snd)

/-- **Closure under composition.** If `c` computes `F` and `d` computes `G` relative to `p`, then
`streamComp d c` computes `G ∘ F` relative to `p`. -/
theorem ComputesStream.comp {p : ℕ →. ℕ} {c d : Code} {F G : (ℕ → ℕ) →. (ℕ → ℕ)}
    (hd : ComputesStream p d G) (hc : ComputesStream p c F) :
    ComputesStream p (streamComp d c) (G.comp F) := by
  intro x z hz
  obtain ⟨y, hy, hz⟩ := Part.mem_bind_iff.1 (PFun.comp_apply G F x ▸ hz)
  rw [streamComp, eval_subst, eval_join, eval_joinLeft, hc x y hy, hd y z hz]

/-- A code computing `F` relative to `p` gives one computing `F` relative to `q`, given a code `a`
that computes `p` relative to `q`. -/
theorem ComputesStream.subst {p q : ℕ →. ℕ} {a c : Code} {F : (ℕ → ℕ) →. (ℕ → ℕ)}
    (ha : eval q a = p) (hc : ComputesStream p c F) :
    ComputesStream q (c.subst (join (a.subst joinLeft) joinRight)) F := by
  intro x y hy
  rw [eval_subst, eval_join, eval_subst, eval_joinLeft, ha, eval_joinRight, hc x y hy]

/-! ### Continuity on the domain -/

/-- **Computable maps are continuous on their domain**, entrywise: each output entry is constant on
the inputs of the domain in some cylinder around `x`. -/
theorem ComputesStream.exists_cylinder {p : ℕ → ℕ} {c : Code} {F : (ℕ → ℕ) →. (ℕ → ℕ)}
    (h : ComputesStream p c F) {x y : ℕ → ℕ} (hy : y ∈ F x) (n : ℕ) :
    ∃ N, ∀ x' ∈ cylinder x N, ∀ y' ∈ F x', y' n = y n := by
  obtain ⟨N, hN⟩ := exists_cylinder_of_mem_eval_join (c := c) (n := n) (v := y n)
    (by rw [h x y hy]; exact Part.mem_some _)
  refine ⟨N, fun x' hx' y' hy' => Part.mem_unique ?_ (hN x' hx')⟩
  rw [h x' y' hy']
  exact Part.mem_some _

/-- **The domain of a computation is a Gδ set**: the inputs on which a code converges at every
entry, relative to a total oracle, form a countable intersection of open sets. -/
theorem isGδ_dom_evalStream (p : ℕ → ℕ) (c : Code) : IsGδ (evalStream p c).Dom := by
  have hdom : (evalStream p c).Dom =
      ⋂ n, {x : ℕ → ℕ | (eval ((p : ℕ →. ℕ) ⊕ (x : ℕ →. ℕ)) c n).Dom} := by
    ext x
    simp [PFun.Dom, evalStream]
  rw [hdom]
  refine IsGδ.iInter_of_isOpen fun n => isOpen_iff_forall_mem_open.2 fun x hx => ?_
  obtain ⟨N, hN⟩ := exists_cylinder_of_mem_eval_join (Part.get_mem hx)
  exact ⟨cylinder x N, fun y hy => Part.dom_iff_mem.2 ⟨_, hN y hy⟩, isOpen_cylinder _ x N,
    self_mem_cylinder x N⟩

end Code

/-! ### Computability relative to an oracle -/

/-- The partial map `F` on Baire space is *computable relative to the oracle `p`* when some code
computes it relative to `p`. -/
@[expose] def StreamComputableIn (p : ℕ →. ℕ) (F : (ℕ → ℕ) →. (ℕ → ℕ)) : Prop :=
  ∃ c, Code.ComputesStream p c F

/-- The partial map `F` on Baire space is *computable* when some code computes it relative to the
oracle that is constantly `0`, that is, without oracle information
(`streamComputable_iff_exists_computable`). -/
@[expose] def StreamComputable (F : (ℕ → ℕ) →. (ℕ → ℕ)) : Prop :=
  StreamComputableIn ((fun _ => 0 : ℕ → ℕ) : ℕ →. ℕ) F

/-- Computability relative to `p` passes to every oracle `q` that computes `p`. -/
theorem StreamComputableIn.of_turingReducible {p q : ℕ →. ℕ} {F : (ℕ → ℕ) →. (ℕ → ℕ)}
    (hpq : p ≤ᵀ q) (hF : StreamComputableIn p F) : StreamComputableIn q F := by
  obtain ⟨a, ha⟩ := Code.turingReducible_iff_exists_code.1 hpq
  obtain ⟨c, hc⟩ := hF
  exact ⟨_, hc.subst ha⟩

/-- **Closure under composition.** Maps computable relative to `p` and to `q` compose to a map
computable relative to `p ⊕ q`. -/
theorem StreamComputableIn.comp {p q : ℕ →. ℕ} {F G : (ℕ → ℕ) →. (ℕ → ℕ)}
    (hG : StreamComputableIn q G) (hF : StreamComputableIn p F) :
    StreamComputableIn (p ⊕ q) (G.comp F) := by
  obtain ⟨d, hd⟩ := hG.of_turingReducible (_root_.right_le_join p q)
  obtain ⟨c, hc⟩ := hF.of_turingReducible (_root_.left_le_join p q)
  exact ⟨_, hd.comp hc⟩

/-- **Closure under composition** of computable maps. -/
theorem StreamComputable.comp {F G : (ℕ → ℕ) →. (ℕ → ℕ)} (hG : StreamComputable G)
    (hF : StreamComputable F) : StreamComputable (G.comp F) := by
  obtain ⟨d, hd⟩ := hG
  obtain ⟨c, hc⟩ := hF
  exact ⟨_, hd.comp hc⟩

/-- A map is computable exactly when it is computable relative to some computable oracle. -/
theorem streamComputable_iff_exists_computable {F : (ℕ → ℕ) →. (ℕ → ℕ)} :
    StreamComputable F ↔ ∃ p : ℕ → ℕ, Computable p ∧ StreamComputableIn p F := by
  refine ⟨fun h => ⟨fun _ => 0, Computable.const 0, h⟩, fun ⟨p, hp, c, hc⟩ => ?_⟩
  obtain ⟨a, ha⟩ := Code.HasUniformCode.of_computable
    (o := fun _ : Unit => ((fun _ => 0 : ℕ → ℕ) : ℕ →. ℕ)) hp
  exact ⟨_, hc.subst (ha ())⟩

/-- **Computable maps are continuous on their domain.** A map computable relative to a total
oracle, restricted to its domain, is continuous. -/
theorem StreamComputableIn.continuous_get {p : ℕ → ℕ} {F : (ℕ → ℕ) →. (ℕ → ℕ)}
    (hF : StreamComputableIn p F) : Continuous fun x : F.Dom => (F x).get x.2 := by
  obtain ⟨c, hc⟩ := hF
  refine continuous_pi fun n => IsLocallyConstant.continuous <|
    (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
  obtain ⟨N, hN⟩ := hc.exists_cylinder (Part.get_mem x.2) n
  have hU : cylinder x.1 N ∈ nhds x.1 :=
    (isOpen_cylinder _ x.1 N).mem_nhds (self_mem_cylinder x.1 N)
  filter_upwards [continuous_subtype_val.continuousAt.preimage_mem_nhds hU] with y hy
  exact hN y.1 hy _ (Part.get_mem y.2)

/-- **The continuity theorem.** A total map on Baire space is continuous if and only if it is
computable relative to some oracle. -/
theorem continuous_iff_streamComputableIn {F : (ℕ → ℕ) → ℕ → ℕ} :
    Continuous F ↔ ∃ p : ℕ → ℕ, StreamComputableIn p F := by
  simp only [StreamComputableIn, Code.computesStream_coe_iff]
  exact Code.continuous_iff_exists_code

/-! ### The effective form -/

namespace Code

/-- The associate read off a code `c` relative to the input alone: it answers `⟨n, σ⟩` with
`v + 1` when the stage-`|σ|` evaluation of `c` at `n` against the oracle prefix `σ` returns `v`,
and with `0` otherwise. -/
private def associate (c : Code) (m : ℕ) : ℕ :=
  ((evaln (ofNat (List ℕ) m.unpair.2) (ofNat (List ℕ) m.unpair.2).length c m.unpair.1).map
    (· + 1)).getD 0

private theorem computable_associate (c : Code) : Computable (associate c) := by
  have hσ : Primrec fun m : ℕ => ofNat (List ℕ) m.unpair.2 :=
    (_root_.Primrec.ofNat (List ℕ)).comp (_root_.Primrec.snd.comp _root_.Primrec.unpair)
  open _root_.Primrec in
  exact (option_getD.comp (option_map (primrec_evaln.comp (hσ.pair
    (((list_length.comp hσ).pair (const c)).pair (fst.comp _root_.Primrec.unpair))))
    (_root_.Primrec.succ.comp snd).to₂) (const 0)).to_comp

private theorem associate_apply (c : Code) (x : ℕ → ℕ) (n k : ℕ) :
    associate c (Nat.pair n (encode (prefixOf x k))) =
      ((evaln (prefixOf x k) k c n).map (· + 1)).getD 0 := by
  simp [associate, length_prefixOf]

/-- The associate read off a code that computes `F` relative to the input alone is an associate
of `F`. -/
private theorem isAssociate_associate {c : Code} {F : (ℕ → ℕ) → ℕ → ℕ}
    (hc : ∀ (x : ℕ → ℕ) n, eval (x : ℕ →. ℕ) c n = Part.some (F x n)) :
    IsAssociate (associate c) F where
  exists_ne_zero x n := by
    obtain ⟨s, hs⟩ := mem_eval_iff_exists_evaln.1 (hc x n ▸ Part.mem_some (F x n))
    exact ⟨s, by simp [associate_apply, Option.mem_def.1 hs]⟩
  eq_of_ne_zero x n k h := by
    rw [associate_apply] at h ⊢
    cases hv : evaln (prefixOf x k) k c n with
    | none => simp [hv] at h
    | some w =>
      have hw := evaln_sound (prefixOf_mem x k) (Option.mem_def.2 hv)
      rw [hc x n, Part.mem_some_iff] at hw
      simp [hw]

end Code

/-- **The effective continuity theorem.** A total map on Baire space is computable exactly when it
has a computable associate. -/
theorem streamComputable_iff_exists_isAssociate {F : (ℕ → ℕ) → ℕ → ℕ} :
    StreamComputable F ↔ ∃ α : ℕ → ℕ, Computable α ∧ Code.IsAssociate α F := by
  refine ⟨fun ⟨c, hc⟩ => ?_, fun ⟨α, hα, hF⟩ => ?_⟩
  · -- Run `c` relative to the input alone, reading the constant oracle `0` from `Code.zero`.
    refine ⟨_, Code.computable_associate (c.subst (Code.join Code.zero Code.oracle)),
      Code.isAssociate_associate fun x n => ?_⟩
    rw [Code.eval_subst, Code.eval_join]
    exact Code.computesStream_coe_iff.1 hc x n
  · obtain ⟨e, he⟩ := Code.exists_code_isAssociate
    exact streamComputable_iff_exists_computable.2
      ⟨α, hα, e, Code.computesStream_coe_iff.2 (he F α hF)⟩

end Nat.RecursiveIn
