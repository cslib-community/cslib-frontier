/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Replacement.Basic

/-!
# Open simulations as graph replacements

An implementation's private wires form the private state of a component. Open simulations give
its preparation and cleanup paths; the ambient naming identifies its boundary with shared graph
edges. This bridges diagram certificates to substitution in arbitrary incidence graphs.

## Main definitions

* `Cslib.Complexity.NCL.Diagram.Replacement.realizes`: a graph replacement from an open diagram.

## Main results

* `Cslib.Complexity.NCL.Diagram.Replacement.realizes`: local graph realization.

## References

* [R. A. Hearn and E. D. Demaine, *PSPACE-completeness of sliding-block puzzles and other
  problems through the nondeterministic constraint logic model of computation*][HearnDemaine2005]
-/

public section

attribute [local implicit_reducible] Cslib.Complexity.NCL.Diagram.Inner
  Cslib.Complexity.NCL.Diagram.instDecidableEqInner

namespace Cslib.Complexity.NCL.Diagram.Replacement

open Relation

variable {a b : List Color} {g : Prim a b} {H : Diagram Prim a b}
variable {E : Type*} [DecidableEq E] (S : OpenSim Prim.interp Prim.interp (gen g) H)
variable (p : (gen g : Diagram Prim a b).Edge → E) (hp : Function.Injective p)

omit [DecidableEq E] in
private theorem inner_path (s : E → Bool) {t u : H.Edge → Bool}
    (ht : Agrees S p s t) (hu : InnerReach Prim.interp H t u) :
    ReflTransGen ((ConstraintGraph.Replacement.component (graph S p)).Step s)
      (restrict S t) (restrict S u) := by
  classical
  induction hu with
  | refl => exact .refl
  | @tail u v hpath hstep ih =>
    have hu := agrees_of_innerReach S p s ht hpath
    have hv := agrees_of_innerReach S p s ht (hpath.tail hstep)
    obtain ⟨hul, hvl, e, he, heq⟩ := hstep
    have hprivate : e ∉ Set.range S.ι := by
      rintro ⟨x, rfl⟩
      exact he (boundary_ι S x)
    apply ih.tail
    refine ⟨(legal_iff S p s _).2 ?_, (legal_iff S p s _).2 ?_, ⟨⟨e, hprivate⟩, ?_⟩⟩
    · simpa only [orient_restrict S p s hu] using hul
    · simpa only [orient_restrict S p s hv] using hvl
    · rw [heq]
      exact reverse_comp_of_injective Subtype.val_injective u ⟨e, hprivate⟩

private theorem orient_reverse (hp : Function.Injective p) (s : E → Bool) (x : Inner S → Bool)
    (i : (gen g : Diagram Prim a b).Edge) :
    orient S p (reverse s (p i)) x = reverse (orient S p s x) (S.ι i) := by
  have hsum : Sum.elim (reverse s (p i)) x = reverse (Sum.elim s x) (.inl (p i)) := by
    funext e
    rcases e with e | e <;> simp [reverse, Function.update]
  unfold orient
  rw [hsum, ← label_ι S p i]
  exact reverse_comp_of_injective (label_injective S hp) (Sum.elim s x) (S.ι i)

/-- An open implementation realizes any ambient vertex with the same boundary legality. -/
def realizesOfLegalIff (spec : Vertex E)
    (hspec : ∀ s, ((gen g).graph Prim.interp).Legal (s ∘ p) ↔ spec.Sat s) :
    Realizes (ConstraintGraph.Replacement.component (graph S p)) spec where
  canon s := restrict S (S.enc (s ∘ p))
  sound {s x} hx := by
    have ht := S.sound ((legal_iff S p s x).1 hx)
    have hboundary : orient S p s x ∘ S.ι = s ∘ p := funext (orient_ι S p s x)
    rw [hboundary] at ht
    exact (hspec _).1 ht
  legal_canon {s} hs := by
    apply (legal_iff S p s _).2
    rw [orient_restrict S p s (t := S.enc (s ∘ p)) (S.enc_ι (s ∘ p))]
    exact S.legal_enc ((hspec _).2 hs)
  move {s} e hs ht := by
    classical
    have hs' := (hspec _).2 hs
    have ht' := (hspec _).2 ht
    by_cases he : e ∈ Set.range p
    · obtain ⟨i, rfl⟩ := he
      have hflip : reverse s (p i) ∘ p = reverse (s ∘ p) i := reverse_comp_of_injective hp s i
      rw [hflip] at ht'
      obtain ⟨u, hpre, hmid, hpost⟩ := S.lift i hs' ht'
      have hu := agrees_of_innerReach S p s (S.enc_ι _) hpre
      have hnew : orient S p (reverse s (p i)) (restrict S u) = reverse u (S.ι i) := by
        rw [orient_reverse S p hp, orient_restrict S p s hu]
      have hv : Agrees S p (reverse s (p i)) (reverse u (S.ι i)) := fun x =>
        (congrFun hnew (S.ι x)).symm.trans (orient_ι S p _ _ x)
      have hrestrict : restrict S (reverse u (S.ι i)) = restrict S u :=
        reverse_comp_of_not_mem_range u (fun x h => x.property ⟨i, h.symm⟩)
      refine ⟨restrict S u, inner_path S p s (S.enc_ι _) hpre, ?_, ?_⟩
      · apply (legal_iff S p _ _).2
        exact hnew.symm ▸ hmid
      · have hr := inner_path S p (reverse s (p i)) hv hpost
        simpa only [hrestrict, ← hflip] using hr
    · have hflip : reverse s e ∘ p = s ∘ p :=
        reverse_comp_of_not_mem_range s (fun i hi => he ⟨i, hi⟩)
      have hcanon : restrict S (S.enc (reverse s e ∘ p)) = restrict S (S.enc (s ∘ p)) :=
        congrArg (fun β => restrict S (S.enc β)) hflip
      refine ⟨restrict S (S.enc (s ∘ p)), .refl, ?_, ?_⟩
      · apply (legal_iff S p _ _).2
        rw [← hcanon, orient_restrict S p _
          (t := S.enc (reverse s e ∘ p)) (S.enc_ι (reverse s e ∘ p))]
        exact S.legal_enc ht'
      · rw [hcanon]
        exact .refl

/-- Canonical private directions are the open implementation's canonical directions. -/
theorem realizesOfLegalIff_canon (spec : Vertex E)
    (hspec : ∀ s, ((gen g).graph Prim.interp).Legal (s ∘ p) ↔ spec.Sat s)
    (s : E → Bool) (e : Inner S) :
    (realizesOfLegalIff S p hp spec hspec).canon s e = S.enc (s ∘ p) e.val := by rfl

/-- An open implementation, placed on injective ambient port names, realizes its source vertex. -/
def realizes (spec : Vertex ((gen g : Diagram Prim a b).Edge))
    (hspec : ∀ β, ((gen g).graph Prim.interp).Legal β ↔ spec.Sat β) :
    Realizes (ConstraintGraph.Replacement.component (graph S p)) (spec.map p) :=
  realizesOfLegalIff S p hp (spec.map p) fun s =>
    (hspec (s ∘ p)).trans (Vertex.sat_map p spec s).symm

end Cslib.Complexity.NCL.Diagram.Replacement
