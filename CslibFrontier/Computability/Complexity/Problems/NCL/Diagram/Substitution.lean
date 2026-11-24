/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Glue
public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.Simulation

/-!
# Substituting diagrams for generators

Replacing every generator of a diagram by a diagram with the same boundary
(`Cslib.Complexity.NCL.Diagram.subst`) preserves and reflects reachability, provided each
replacement implements its generator. This is how [HearnDemaine2005] builds AND/OR graphs from
larger vertices: a crossover from half-crossovers, a protected OR from protected ORs.

The replacements must work together. A wire may join two replaced generators, and reversing it
then needs both replacements to prepare their insides first and to clean them up afterwards. So
the relation between a diagram and its replacement is an open simulation
(`Cslib.Complexity.NCL.Diagram.OpenSim`): the edges of the diagram embed into those of the
replacement, keeping the boundary; every configuration of the replacement restricts to one of the
diagram; every configuration of the diagram extends to one of the replacement; and every move of
the diagram is realized by moves inside the replacement, then the move itself, then moves inside
again. Moves inside keep the boundary, so the moves of two neighbouring replacements can be
interleaved. Open simulations are preserved by stacking and juxtaposition, so substitution is an
open simulation, and every open simulation induces a simulation of constraint graphs.

## Main definitions

* `Cslib.Complexity.NCL.Diagram.InnerReach`: reachability by moves that keep the boundary.
* `Cslib.Complexity.NCL.Diagram.OpenSim`: an open simulation of one diagram by another;
  `Cslib.Complexity.NCL.Diagram.OpenSim.comp`, `Cslib.Complexity.NCL.Diagram.OpenSim.tensor`,
  `Cslib.Complexity.NCL.Diagram.OpenSim.trans`: stacking, juxtaposition and composition.
* `Cslib.Complexity.NCL.Diagram.subst`: replacing every generator by a diagram.

## Main results

* `Cslib.Complexity.NCL.Diagram.openSimSubst`: substitution is an open simulation when each
  replacement implements its generator.
* `Cslib.Complexity.NCL.Diagram.substSimulation`: a simulation of constraint graphs,
  so reachability is preserved and reflected, for any boundary.
* `Cslib.Complexity.NCL.Diagram.Planar.subst`: planar replacements keep a diagram planar.

## References

* [R. A. Hearn and E. D. Demaine, *PSPACE-completeness of sliding-block puzzles and other
  problems through the nondeterministic constraint logic model of computation*][HearnDemaine2005]
-/

public section

namespace Cslib.Complexity.NCL.Diagram

open ConstraintGraph Relation

variable {Γ Γ' Γ'' : List Color → List Color → Type} {I : Interp Γ} {I' : Interp Γ'}
  {I'' : Interp Γ''} {a b c d : List Color}

/-! ### Open simulations -/

variable (I I') in
/-- An **open simulation** of the diagram `D` by `D'`, which has the same boundary: the edges of
`D` embed into those of `D'`, keeping the boundary; every configuration of `D'` restricts to one of
`D`; every configuration of `D` extends to one of `D'`; and every move of `D` is realized by moves
inside `D'`, then the move itself, then moves inside again. -/
structure OpenSim (D : Diagram Γ a b) (D' : Diagram Γ' a b) where
  /-- The edges of `D` as edges of `D'`. -/
  ι : D.Edge → D'.Edge
  ι_injective : Function.Injective ι
  ι_top (i : Fin a.length) : ι (.inl i) = .inl i
  ι_bottom (j : Fin b.length) : ι (D.bottom j) = D'.bottom j
  /-- The configuration of `D'` that extends a configuration of `D`. -/
  enc : (D.Edge → Bool) → D'.Edge → Bool
  enc_ι (s : D.Edge → Bool) (x : D.Edge) : enc s (ι x) = s x
  sound {t : D'.Edge → Bool} : (D'.graph I').Legal t → (D.graph I).Legal (t ∘ ι)
  legal_enc {s : D.Edge → Bool} : (D.graph I).Legal s → (D'.graph I').Legal (enc s)
  lift {s : D.Edge → Bool} (x : D.Edge) : (D.graph I).Legal s → (D.graph I).Legal (reverse s x) →
    ∃ u, InnerReach I' D' (enc s) u ∧ (D'.graph I').Legal (reverse u (ι x)) ∧
      InnerReach I' D' (reverse u (ι x)) (enc (reverse s x))

namespace OpenSim

variable {D₁ : Diagram Γ a b} {D₂ : Diagram Γ b c} {D₁' : Diagram Γ' a b}
  {D₂' : Diagram Γ' b c}

/-- Lifts of false-to-true reversals suffice, since all internal and boundary moves reverse. -/
theorem lift_of_false {D : Diagram Γ a b} {D' : Diagram Γ' a b}
    (ι : D.Edge → D'.Edge) (enc : (D.Edge → Bool) → D'.Edge → Bool)
    (hlegal : ∀ {s}, (D.graph I).Legal s → (D'.graph I').Legal (enc s))
    (hpositive : ∀ s x, s x = false → (D.graph I).Legal s →
      (D.graph I).Legal (reverse s x) →
        ∃ u, InnerReach I' D' (enc s) u ∧ (D'.graph I').Legal (reverse u (ι x)) ∧
          InnerReach I' D' (reverse u (ι x)) (enc (reverse s x)))
    {s : D.Edge → Bool} (x : D.Edge) (hs : (D.graph I).Legal s)
    (ht : (D.graph I).Legal (reverse s x)) :
    ∃ u, InnerReach I' D' (enc s) u ∧ (D'.graph I').Legal (reverse u (ι x)) ∧
      InnerReach I' D' (reverse u (ι x)) (enc (reverse s x)) := by
  let : Std.Symm (InnerStep I' D') := ⟨fun _ _ h => ConstraintGraph.StepOn.symm h⟩
  cases hx : s x with
  | false => exact hpositive s x hx hs ht
  | true =>
    have hγ : reverse s x x = false := by simp only [reverse_self, hx, Bool.not_true]
    have hs' : (D.graph I).Legal (reverse (reverse s x) x) := by
      simpa only [reverse_reverse] using hs
    obtain ⟨u, hp, hf, hq⟩ := hpositive (reverse s x) x hγ ht hs'
    refine ⟨reverse u (ι x), ?_, ?_, ?_⟩
    · simpa only [reverse_reverse] using _root_.symm hq
    · simpa only [reverse_reverse] using InnerReach.legal hp (hlegal ht)
    · simpa only [reverse_reverse] using _root_.symm hp

/-- Created wires stay created wires. -/
theorem ι_inr {D : Diagram Γ a b} {D' : Diagram Γ' a b} (S : OpenSim I I' D D') (e : D.Inner) :
    ∃ e', S.ι (.inr e) = .inr e' := by
  rcases h : S.ι (.inr e) with i | e'
  · exact absurd (S.ι_injective (h.trans (S.ι_top i).symm)) (by simp)
  · exact ⟨e', rfl⟩

/-- The edges of a stack, mapped part by part. -/
@[expose] def compι (S₁ : OpenSim I I' D₁ D₁') (S₂ : OpenSim I I' D₂ D₂') :
    (comp D₁ D₂).Edge → (comp D₁' D₂').Edge
  | .inl i => .inl i
  | .inr (.inl e) => compLeft D₁' D₂' (S₁.ι (.inr e))
  | .inr (.inr e) => compRight D₁' D₂' (S₂.ι (.inr e))

variable (S₁ : OpenSim I I' D₁ D₁') (S₂ : OpenSim I I' D₂ D₂')

theorem compι_compLeft (y : D₁.Edge) :
    compι S₁ S₂ (compLeft D₁ D₂ y) = compLeft D₁' D₂' (S₁.ι y) := by
  rcases y with i | e
  · rw [S₁.ι_top]
    rfl
  · rfl

theorem compι_compRight (z : D₂.Edge) :
    compι S₁ S₂ (compRight D₁ D₂ z) = compRight D₁' D₂' (S₂.ι z) := by
  rcases z with j | e
  · rw [S₂.ι_top]
    exact (compι_compLeft S₁ S₂ _).trans (congrArg _ (S₁.ι_bottom j))
  · rfl

/-- The configuration of the stack of replacements, part by part. -/
@[expose] def compEnc (s : (comp D₁ D₂).Edge → Bool) : (comp D₁' D₂').Edge → Bool :=
  glueComp D₁' D₂' (S₁.enc (s ∘ compLeft D₁ D₂)) (S₂.enc (s ∘ compRight D₁ D₂))

private theorem compEnc_agree (s : (comp D₁ D₂).Edge → Bool) (j : Fin b.length) :
    S₂.enc (s ∘ compRight D₁ D₂) (.inl j) = S₁.enc (s ∘ compLeft D₁ D₂) (D₁'.bottom j) := by
  rw [← S₂.ι_top, S₂.enc_ι, ← S₁.ι_bottom, S₁.enc_ι]
  rfl

private theorem compEnc_compLeft (s : (comp D₁ D₂).Edge → Bool) (y : D₁'.Edge) :
    compEnc S₁ S₂ s (compLeft D₁' D₂' y) = S₁.enc (s ∘ compLeft D₁ D₂) y :=
  glueComp_compLeft ..

private theorem compEnc_compRight (s : (comp D₁ D₂).Edge → Bool) (z : D₂'.Edge) :
    compEnc S₁ S₂ s (compRight D₁' D₂' z) = S₂.enc (s ∘ compRight D₁ D₂) z :=
  glueComp_compRight _ _ _ _ (compEnc_agree S₁ S₂ s) z

theorem compEnc_ι (s : (comp D₁ D₂).Edge → Bool) (x : (comp D₁ D₂).Edge) :
    compEnc S₁ S₂ s (compι S₁ S₂ x) = s x := by
  rcases comp_cases_compRight x with ⟨y, rfl⟩ | ⟨z, rfl⟩
  · rw [compι_compLeft, compEnc_compLeft, S₁.enc_ι]
    rfl
  · rw [compι_compRight, compEnc_compRight, S₂.enc_ι]
    rfl

theorem compι_injective : Function.Injective (compι S₁ S₂) :=
  (Function.surjective_comp_right_iff_injective (γ := Bool)).1 fun s =>
    ⟨compEnc S₁ S₂ s, funext (compEnc_ι S₁ S₂ s)⟩

theorem comp_sound {t : (comp D₁' D₂').Edge → Bool} (ht : ((comp D₁' D₂').graph I').Legal t) :
    ((comp D₁ D₂).graph I).Legal (t ∘ compι S₁ S₂) := by
  obtain ⟨h₁, h₂⟩ := (legal_comp_iff _ _ _).1 ht
  refine (legal_comp_iff _ _ _).2 ⟨?_, ?_⟩
  · rw [show (t ∘ compι S₁ S₂) ∘ compLeft D₁ D₂ = (t ∘ compLeft D₁' D₂') ∘ S₁.ι from
      funext fun y => congrArg t (compι_compLeft S₁ S₂ y)]
    exact S₁.sound h₁
  · rw [show (t ∘ compι S₁ S₂) ∘ compRight D₁ D₂ = (t ∘ compRight D₁' D₂') ∘ S₂.ι from
      funext fun z => congrArg t (compι_compRight S₁ S₂ z)]
    exact S₂.sound h₂

theorem comp_legal_enc {s : (comp D₁ D₂).Edge → Bool} (hs : ((comp D₁ D₂).graph I).Legal s) :
    ((comp D₁' D₂').graph I').Legal (compEnc S₁ S₂ s) := by
  obtain ⟨h₁, h₂⟩ := (legal_comp_iff _ _ _).1 hs
  exact legal_glueComp (S₁.legal_enc h₁) (S₂.legal_enc h₂) (compEnc_agree S₁ S₂ s)

private theorem comp_lift_left {s : (comp D₁ D₂).Edge → Bool} {y : D₁.Edge}
    (hy : ∀ j, y ≠ D₁.bottom j) (hs : ((comp D₁ D₂).graph I).Legal s)
    (hs' : ((comp D₁ D₂).graph I).Legal (reverse s (compLeft D₁ D₂ y))) :
    ∃ u, InnerReach I' (comp D₁' D₂') (compEnc S₁ S₂ s) u ∧
      ((comp D₁' D₂').graph I').Legal (reverse u (compι S₁ S₂ (compLeft D₁ D₂ y))) ∧
      InnerReach I' (comp D₁' D₂') (reverse u (compι S₁ S₂ (compLeft D₁ D₂ y)))
        (compEnc S₁ S₂ (reverse s (compLeft D₁ D₂ y))) := by
  obtain ⟨h₁, h₂⟩ := (legal_comp_iff _ _ _).1 hs
  obtain ⟨h₁', -⟩ := (legal_comp_iff _ _ _).1 hs'
  rw [reverse_compLeft_comp] at h₁'
  obtain ⟨u₁, hp, hf, hq⟩ := S₁.lift y h₁ h₁'
  have hne : ∀ j, S₁.ι y ≠ D₁'.bottom j := fun j h =>
    hy j (S₁.ι_injective (h.trans (S₁.ι_bottom j).symm))
  have hag : ∀ j, S₂.enc (s ∘ compRight D₁ D₂) (.inl j) = reverse u₁ (S₁.ι y) (D₁'.bottom j) :=
    fun j => by
      rw [reverse_of_ne _ (Ne.symm (hne j)), InnerReach.boundary hp (Or.inr ⟨j, rfl⟩)]
      exact compEnc_agree S₁ S₂ s j
  have hag₀ : ∀ j, S₂.enc (s ∘ compRight D₁ D₂) (.inl j) = u₁ (D₁'.bottom j) := fun j =>
    (hag j).trans (reverse_of_ne _ (Ne.symm (hne j)))
  refine ⟨glueComp D₁' D₂' u₁ (S₂.enc (s ∘ compRight D₁ D₂)),
    innerReach_glueComp_left hp (S₂.legal_enc h₂) (compEnc_agree S₁ S₂ s), ?_, ?_⟩ <;>
    rw [compι_compLeft, ← glueComp_reverse_left]
  · exact legal_glueComp hf (S₂.legal_enc h₂) hag
  · have := innerReach_glueComp_left hq (S₂.legal_enc h₂) hag
    rwa [compEnc, reverse_compLeft_comp, reverse_compLeft_comp_compRight _ _ _ hy]

private theorem comp_lift_right {s : (comp D₁ D₂).Edge → Bool} {e : D₂.Inner}
    (hs : ((comp D₁ D₂).graph I).Legal s)
    (hs' : ((comp D₁ D₂).graph I).Legal (reverse s (.inr (.inr e)))) :
    ∃ u, InnerReach I' (comp D₁' D₂') (compEnc S₁ S₂ s) u ∧
      ((comp D₁' D₂').graph I').Legal (reverse u (compι S₁ S₂ (.inr (.inr e)))) ∧
      InnerReach I' (comp D₁' D₂') (reverse u (compι S₁ S₂ (.inr (.inr e))))
        (compEnc S₁ S₂ (reverse s (.inr (.inr e)))) := by
  obtain ⟨h₁, h₂⟩ := (legal_comp_iff _ _ _).1 hs
  obtain ⟨-, h₂'⟩ := (legal_comp_iff _ _ _).1 hs'
  rw [show (reverse s (.inr (.inr e)) ∘ compRight D₁ D₂) =
    reverse (s ∘ compRight D₁ D₂) (.inr e) from reverse_compRight_comp _ _ s (.inr e)] at h₂'
  obtain ⟨u₂, hp, hf, hq⟩ := S₂.lift (.inr e) h₂ h₂'
  obtain ⟨e', he'⟩ := S₂.ι_inr e
  rw [he'] at hf hq
  have hag : ∀ j, reverse u₂ (.inr e') (.inl j) = S₁.enc (s ∘ compLeft D₁ D₂) (D₁'.bottom j) :=
    fun j => by
      rw [reverse_of_ne _ (by simp), InnerReach.boundary hp (Or.inl ⟨j, rfl⟩)]
      exact compEnc_agree S₁ S₂ s j
  have hc : compι S₁ S₂ (.inr (.inr e)) = .inr (.inr e') := by
    change compRight D₁' D₂' (S₂.ι (.inr e)) = _
    rw [he']
    rfl
  refine ⟨glueComp D₁' D₂' (S₁.enc (s ∘ compLeft D₁ D₂)) u₂,
    innerReach_glueComp_right hp (S₁.legal_enc h₁) (compEnc_agree S₁ S₂ s), ?_, ?_⟩ <;>
    rw [hc, ← glueComp_reverse_right]
  · exact legal_glueComp (S₁.legal_enc h₁) hf hag
  · have := innerReach_glueComp_right hq (S₁.legal_enc h₁) hag
    rwa [compEnc, reverse_inr_comp_compLeft,
      show (reverse s (.inr (.inr e)) ∘ compRight D₁ D₂) =
        reverse (s ∘ compRight D₁ D₂) (.inr e) from reverse_compRight_comp _ _ s (.inr e)]

/-- A shared wire: both parts prepare, the wire is reversed, both parts clean up. -/
private theorem comp_lift_shared {s : (comp D₁ D₂).Edge → Bool} (j : Fin b.length)
    (hs : ((comp D₁ D₂).graph I).Legal s)
    (hs' : ((comp D₁ D₂).graph I).Legal (reverse s (compLeft D₁ D₂ (D₁.bottom j)))) :
    ∃ u, InnerReach I' (comp D₁' D₂') (compEnc S₁ S₂ s) u ∧
      ((comp D₁' D₂').graph I').Legal (reverse u (compι S₁ S₂ (compLeft D₁ D₂ (D₁.bottom j)))) ∧
      InnerReach I' (comp D₁' D₂') (reverse u (compι S₁ S₂ (compLeft D₁ D₂ (D₁.bottom j))))
        (compEnc S₁ S₂ (reverse s (compLeft D₁ D₂ (D₁.bottom j)))) := by
  set s₁ := s ∘ compLeft D₁ D₂
  set s₂ := s ∘ compRight D₁ D₂
  have e₁ : reverse s (compLeft D₁ D₂ (D₁.bottom j)) ∘ compLeft D₁ D₂ =
      reverse s₁ (D₁.bottom j) := reverse_compLeft_comp ..
  have e₂ : reverse s (compLeft D₁ D₂ (D₁.bottom j)) ∘ compRight D₁ D₂ =
      reverse s₂ (.inl j) := reverse_compRight_comp _ _ s (.inl j)
  obtain ⟨h₁, h₂⟩ := (legal_comp_iff _ _ _).1 hs
  obtain ⟨h₁', h₂'⟩ := (legal_comp_iff _ _ _).1 hs'
  rw [e₁] at h₁'
  rw [e₂] at h₂'
  obtain ⟨u₁, hp₁, hf₁, hq₁⟩ := S₁.lift (D₁.bottom j) h₁ h₁'
  obtain ⟨u₂, hp₂, hf₂, hq₂⟩ := S₂.lift (.inl j) h₂ h₂'
  rw [S₁.ι_bottom] at hf₁ hq₁
  rw [S₂.ι_top] at hf₂ hq₂
  -- the two prepared parts agree on the shared wires, before and after the reversal
  have hu : ∀ k, u₂ (.inl k) = u₁ (D₁'.bottom k) := fun k => by
    rw [InnerReach.boundary hp₂ (Or.inl ⟨k, rfl⟩), InnerReach.boundary hp₁ (Or.inr ⟨k, rfl⟩)]
    exact compEnc_agree S₁ S₂ s k
  have hu' : ∀ k, reverse u₂ (.inl j) (.inl k) = reverse u₁ (D₁'.bottom j) (D₁'.bottom k) :=
    fun k => by
      by_cases hk : k = j
      · subst hk
        rw [reverse_self, reverse_self, hu]
      · rw [reverse_of_ne _ (by simpa using hk),
          reverse_of_ne _ fun h => hk (bottom_injective D₁' h), hu]
  have hc : compι S₁ S₂ (compLeft D₁ D₂ (D₁.bottom j)) = compLeft D₁' D₂' (D₁'.bottom j) := by
    rw [compι_compLeft, S₁.ι_bottom]
  have hflip : reverse (glueComp D₁' D₂' u₁ u₂) (compLeft D₁' D₂' (D₁'.bottom j)) =
      glueComp D₁' D₂' (reverse u₁ (D₁'.bottom j)) (reverse u₂ (.inl j)) := by
    rw [← glueComp_reverse_left]
    exact glueComp_congr_right _ _ _ fun e => (reverse_of_ne _ (by simp)).symm
  refine ⟨glueComp D₁' D₂' u₁ u₂,
    (innerReach_glueComp_left hp₁ (S₂.legal_enc h₂) (compEnc_agree S₁ S₂ s)).trans
      (innerReach_glueComp_right hp₂ (InnerReach.legal hp₁ (S₁.legal_enc h₁)) fun k =>
        (compEnc_agree S₁ S₂ s k).trans (InnerReach.boundary hp₁ (Or.inr ⟨k, rfl⟩)).symm),
    ?_, ?_⟩ <;>
    rw [hc, hflip]
  · exact legal_glueComp hf₁ hf₂ hu'
  · have hv : ∀ k, reverse u₂ (.inl j) (.inl k) =
        S₁.enc (reverse s₁ (D₁.bottom j)) (D₁'.bottom k) := fun k =>
      (hu' k).trans (InnerReach.boundary hq₁ (Or.inr ⟨k, rfl⟩)).symm
    have := (innerReach_glueComp_left hq₁ hf₂ hu').trans
      (innerReach_glueComp_right hq₂ (S₁.legal_enc h₁') hv)
    rwa [compEnc, e₁, e₂]

end OpenSim

/-- **Stacking preserves open simulations.** -/
@[expose] def OpenSim.comp {D₁ : Diagram Γ a b} {D₂ : Diagram Γ b c} {D₁' : Diagram Γ' a b}
    {D₂' : Diagram Γ' b c} (S₁ : OpenSim I I' D₁ D₁') (S₂ : OpenSim I I' D₂ D₂') :
    OpenSim I I' (comp D₁ D₂) (comp D₁' D₂') where
  ι := OpenSim.compι S₁ S₂
  ι_injective := OpenSim.compι_injective S₁ S₂
  ι_top _ := rfl
  ι_bottom j := by rw [bottom_comp, bottom_comp, OpenSim.compι_compRight, S₂.ι_bottom]
  enc := OpenSim.compEnc S₁ S₂
  enc_ι := OpenSim.compEnc_ι S₁ S₂
  sound := OpenSim.comp_sound S₁ S₂
  legal_enc := OpenSim.comp_legal_enc S₁ S₂
  lift x hs hs' := by
    rcases comp_cases_compRight x with ⟨y, rfl⟩ | ⟨z, rfl⟩
    · by_cases hy : ∃ j, y = D₁.bottom j
      · obtain ⟨j, rfl⟩ := hy
        exact OpenSim.comp_lift_shared S₁ S₂ j hs hs'
      · exact OpenSim.comp_lift_left S₁ S₂ (fun j h => hy ⟨j, h⟩) hs hs'
    · rcases z with j | e
      · exact OpenSim.comp_lift_shared S₁ S₂ j hs hs'
      · exact OpenSim.comp_lift_right S₁ S₂ hs hs'

/-! ### Juxtaposition -/

namespace OpenSim

variable {D₁ : Diagram Γ a b} {D₂ : Diagram Γ c d} {D₁' : Diagram Γ' a b}
  {D₂' : Diagram Γ' c d}

/-- The edges of a juxtaposition, mapped part by part. -/
@[expose] def tensorι (S₁ : OpenSim I I' D₁ D₁') (S₂ : OpenSim I I' D₂ D₂') :
    (tensor D₁ D₂).Edge → (tensor D₁' D₂').Edge
  | .inl i => .inl i
  | .inr (.inl e) => tensorLeft D₁' D₂' (S₁.ι (.inr e))
  | .inr (.inr e) => tensorRight D₁' D₂' (S₂.ι (.inr e))

variable (S₁ : OpenSim I I' D₁ D₁') (S₂ : OpenSim I I' D₂ D₂')

theorem tensorι_tensorLeft (y : D₁.Edge) :
    tensorι S₁ S₂ (tensorLeft D₁ D₂ y) = tensorLeft D₁' D₂' (S₁.ι y) := by
  rcases y with i | e
  · rw [S₁.ι_top]
    rfl
  · rfl

theorem tensorι_tensorRight (z : D₂.Edge) :
    tensorι S₁ S₂ (tensorRight D₁ D₂ z) = tensorRight D₁' D₂' (S₂.ι z) := by
  rcases z with i | e
  · rw [S₂.ι_top]
    rfl
  · rfl

/-- The configuration of the juxtaposition of replacements, part by part. -/
@[expose] def tensorEnc (s : (tensor D₁ D₂).Edge → Bool) : (tensor D₁' D₂').Edge → Bool :=
  glueTensor D₁' D₂' (S₁.enc (s ∘ tensorLeft D₁ D₂)) (S₂.enc (s ∘ tensorRight D₁ D₂))

theorem tensorEnc_ι (s : (tensor D₁ D₂).Edge → Bool) (x : (tensor D₁ D₂).Edge) :
    tensorEnc S₁ S₂ s (tensorι S₁ S₂ x) = s x := by
  rcases tensor_cases x with ⟨y, rfl⟩ | ⟨z, rfl⟩
  · rw [tensorι_tensorLeft, tensorEnc, glueTensor_tensorLeft, S₁.enc_ι]
    rfl
  · rw [tensorι_tensorRight, tensorEnc, glueTensor_tensorRight, S₂.enc_ι]
    rfl

theorem tensorι_injective : Function.Injective (tensorι S₁ S₂) :=
  (Function.surjective_comp_right_iff_injective (γ := Bool)).1 fun s =>
    ⟨tensorEnc S₁ S₂ s, funext (tensorEnc_ι S₁ S₂ s)⟩

theorem tensor_sound {t : (tensor D₁' D₂').Edge → Bool}
    (ht : ((tensor D₁' D₂').graph I').Legal t) :
    ((tensor D₁ D₂).graph I).Legal (t ∘ tensorι S₁ S₂) := by
  obtain ⟨h₁, h₂⟩ := (legal_tensor_iff _ _ _).1 ht
  refine (legal_tensor_iff _ _ _).2 ⟨?_, ?_⟩
  · rw [show (t ∘ tensorι S₁ S₂) ∘ tensorLeft D₁ D₂ = (t ∘ tensorLeft D₁' D₂') ∘ S₁.ι from
      funext fun y => congrArg t (tensorι_tensorLeft S₁ S₂ y)]
    exact S₁.sound h₁
  · rw [show (t ∘ tensorι S₁ S₂) ∘ tensorRight D₁ D₂ = (t ∘ tensorRight D₁' D₂') ∘ S₂.ι from
      funext fun z => congrArg t (tensorι_tensorRight S₁ S₂ z)]
    exact S₂.sound h₂

theorem tensor_legal_enc {s : (tensor D₁ D₂).Edge → Bool}
    (hs : ((tensor D₁ D₂).graph I).Legal s) :
    ((tensor D₁' D₂').graph I').Legal (tensorEnc S₁ S₂ s) := by
  obtain ⟨h₁, h₂⟩ := (legal_tensor_iff _ _ _).1 hs
  exact legal_glueTensor (S₁.legal_enc h₁) (S₂.legal_enc h₂)

private theorem tensor_lift_left {s : (tensor D₁ D₂).Edge → Bool} (y : D₁.Edge)
    (hs : ((tensor D₁ D₂).graph I).Legal s)
    (hs' : ((tensor D₁ D₂).graph I).Legal (reverse s (tensorLeft D₁ D₂ y))) :
    ∃ u, InnerReach I' (tensor D₁' D₂') (tensorEnc S₁ S₂ s) u ∧
      ((tensor D₁' D₂').graph I').Legal (reverse u (tensorι S₁ S₂ (tensorLeft D₁ D₂ y))) ∧
      InnerReach I' (tensor D₁' D₂') (reverse u (tensorι S₁ S₂ (tensorLeft D₁ D₂ y)))
        (tensorEnc S₁ S₂ (reverse s (tensorLeft D₁ D₂ y))) := by
  obtain ⟨h₁, h₂⟩ := (legal_tensor_iff _ _ _).1 hs
  obtain ⟨h₁', -⟩ := (legal_tensor_iff _ _ _).1 hs'
  rw [reverse_tensorLeft_comp] at h₁'
  obtain ⟨u₁, hp, hf, hq⟩ := S₁.lift y h₁ h₁'
  refine ⟨glueTensor D₁' D₂' u₁ (S₂.enc (s ∘ tensorRight D₁ D₂)),
    innerReach_glueTensor_left hp (S₂.legal_enc h₂), ?_, ?_⟩ <;>
    rw [tensorι_tensorLeft, ← glueTensor_reverse_left]
  · exact legal_glueTensor hf (S₂.legal_enc h₂)
  · have := innerReach_glueTensor_left hq (S₂.legal_enc h₂)
    rwa [tensorEnc, reverse_tensorLeft_comp, reverse_tensorLeft_comp_tensorRight]

private theorem tensor_lift_right {s : (tensor D₁ D₂).Edge → Bool} (z : D₂.Edge)
    (hs : ((tensor D₁ D₂).graph I).Legal s)
    (hs' : ((tensor D₁ D₂).graph I).Legal (reverse s (tensorRight D₁ D₂ z))) :
    ∃ u, InnerReach I' (tensor D₁' D₂') (tensorEnc S₁ S₂ s) u ∧
      ((tensor D₁' D₂').graph I').Legal (reverse u (tensorι S₁ S₂ (tensorRight D₁ D₂ z))) ∧
      InnerReach I' (tensor D₁' D₂') (reverse u (tensorι S₁ S₂ (tensorRight D₁ D₂ z)))
        (tensorEnc S₁ S₂ (reverse s (tensorRight D₁ D₂ z))) := by
  obtain ⟨h₁, h₂⟩ := (legal_tensor_iff _ _ _).1 hs
  obtain ⟨-, h₂'⟩ := (legal_tensor_iff _ _ _).1 hs'
  rw [reverse_tensorRight_comp] at h₂'
  obtain ⟨u₂, hp, hf, hq⟩ := S₂.lift z h₂ h₂'
  refine ⟨glueTensor D₁' D₂' (S₁.enc (s ∘ tensorLeft D₁ D₂)) u₂,
    innerReach_glueTensor_right hp (S₁.legal_enc h₁), ?_, ?_⟩ <;>
    rw [tensorι_tensorRight, ← glueTensor_reverse_right]
  · exact legal_glueTensor (S₁.legal_enc h₁) hf
  · have := innerReach_glueTensor_right hq (S₁.legal_enc h₁)
    rwa [tensorEnc, reverse_tensorRight_comp, reverse_tensorRight_comp_tensorLeft]

end OpenSim

/-- **Juxtaposition preserves open simulations.** -/
@[expose] def OpenSim.tensor {D₁ : Diagram Γ a b} {D₂ : Diagram Γ c d} {D₁' : Diagram Γ' a b}
    {D₂' : Diagram Γ' c d} (S₁ : OpenSim I I' D₁ D₁') (S₂ : OpenSim I I' D₂ D₂') :
    OpenSim I I' (tensor D₁ D₂) (tensor D₁' D₂') where
  ι := OpenSim.tensorι S₁ S₂
  ι_injective := OpenSim.tensorι_injective S₁ S₂
  ι_top _ := rfl
  ι_bottom j := by
    obtain ⟨j, rfl⟩ := (List.appendIndexEquiv b d).surjective j
    rcases j with j | j
    · rw [bottom_tensor_left, bottom_tensor_left, OpenSim.tensorι_tensorLeft, S₁.ι_bottom]
    · rw [bottom_tensor_right, bottom_tensor_right, OpenSim.tensorι_tensorRight, S₂.ι_bottom]
  enc := OpenSim.tensorEnc S₁ S₂
  enc_ι := OpenSim.tensorEnc_ι S₁ S₂
  sound := OpenSim.tensor_sound S₁ S₂
  legal_enc := OpenSim.tensor_legal_enc S₁ S₂
  lift x hs hs' := by
    rcases tensor_cases x with ⟨y, rfl⟩ | ⟨z, rfl⟩
    · exact OpenSim.tensor_lift_left S₁ S₂ y hs hs'
    · exact OpenSim.tensor_lift_right S₁ S₂ z hs hs'

/-! ### Composition -/

namespace OpenSim

variable {D : Diagram Γ a b} {D' : Diagram Γ' a b} {D'' : Diagram Γ'' a b}

/-- An edge off the boundary is mapped off the boundary. -/
private theorem not_isBoundary_ι (S : OpenSim I I' D D') {y : D.Edge} (hy : ¬D.IsBoundary y) :
    ¬D'.IsBoundary (S.ι y) := by
  rintro (⟨i, h⟩ | ⟨j, h⟩)
  · exact hy (Or.inl ⟨i, S.ι_injective (h.trans (S.ι_top i).symm)⟩)
  · exact hy (Or.inr ⟨j, S.ι_injective (h.trans (S.ι_bottom j).symm)⟩)

/-- Moves inside are realized by moves inside. -/
theorem innerReach_enc (S : OpenSim I I' D D') {t t' : D.Edge → Bool}
    (h : InnerReach I D t t') : InnerReach I' D' (S.enc t) (S.enc t') := by
  induction h with
  | refl => exact .refl
  | @tail u u' hr hs ih =>
    obtain ⟨hu, hu', y, hy, rfl⟩ := hs
    obtain ⟨v, hp, hf, hq⟩ := S.lift y hu hu'
    exact ih.trans (hp.trans (ReflTransGen.head
      ⟨InnerReach.legal hp (S.legal_enc hu), hf, _, S.not_isBoundary_ι hy, rfl⟩ hq))

/-- Every diagram simulates itself. -/
@[expose] def refl (D : Diagram Γ a b) : OpenSim I I D D where
  ι x := x
  ι_injective _ _ h := h
  ι_top _ := rfl
  ι_bottom _ := rfl
  enc s := s
  enc_ι _ _ := rfl
  sound h := h
  legal_enc h := h
  lift _ _ hs' := ⟨_, .refl, hs', .refl⟩

/-- **Open simulations compose.** -/
@[expose] def trans (S : OpenSim I I' D D') (T : OpenSim I' I'' D' D'') : OpenSim I I'' D D'' where
  ι := T.ι ∘ S.ι
  ι_injective := T.ι_injective.comp S.ι_injective
  ι_top i := by simp only [Function.comp_apply, S.ι_top, T.ι_top]
  ι_bottom j := by simp only [Function.comp_apply, S.ι_bottom, T.ι_bottom]
  enc := T.enc ∘ S.enc
  enc_ι s x := by simp only [Function.comp_apply, T.enc_ι, S.enc_ι]
  sound h := S.sound (T.sound h)
  legal_enc h := T.legal_enc (S.legal_enc h)
  lift x hs hs' := by
    obtain ⟨u, hp, hf, hq⟩ := S.lift x hs hs'
    obtain ⟨v, hp', hf', hq'⟩ := T.lift (S.ι x) (InnerReach.legal hp (S.legal_enc hs)) hf
    exact ⟨v, (T.innerReach_enc hp).trans hp', hf', hq'.trans (T.innerReach_enc hq)⟩

end OpenSim

/-! ### Substitution -/

/-- Moves inside are moves. -/
theorem InnerReach.reachable {D : Diagram Γ a b} {t t' : D.Edge → Bool}
    (h : InnerReach I D t t') : (D.graph I).Reachable t t' :=
  ConstraintGraph.ReachableOn.reachable h

/-- Wires alone simulate wires alone. -/
@[expose] def OpenSim.idWires (a : List Color) : OpenSim I I' (id a : Diagram Γ a a) (id a) where
  ι x := x
  ι_injective _ _ h := h
  ι_top _ := rfl
  ι_bottom _ := rfl
  enc s := s
  enc_ι _ _ := rfl
  sound _ := legal_id _ _
  legal_enc _ := legal_id _ _
  lift _ _ _ := ⟨_, .refl, legal_id _ _, .refl⟩

/-- A crossing simulates a crossing. -/
@[expose] def OpenSim.swapWires (x y : Color) :
    OpenSim I I' (swap x y : Diagram Γ _ _) (swap x y) where
  ι e := e
  ι_injective _ _ h := h
  ι_top _ := rfl
  ι_bottom _ := rfl
  enc s := s
  enc_ι _ _ := rfl
  sound _ := legal_swap _ _ _
  legal_enc _ := legal_swap _ _ _
  lift _ _ _ := ⟨_, .refl, legal_swap _ _ _, .refl⟩

/-- Replace every generator `g` by the diagram `H g`. -/
@[expose] def subst (H : ∀ {a b : List Color}, Γ a b → Diagram Γ' a b) :
    {a b : List Color} → Diagram Γ a b → Diagram Γ' a b
  | _, _, gen g => H g
  | _, _, id a => id a
  | _, _, swap x y => swap x y
  | _, _, comp D₁ D₂ => comp (subst H D₁) (subst H D₂)
  | _, _, tensor D₁ D₂ => tensor (subst H D₁) (subst H D₂)

/-- Replacing generators by planar diagrams keeps a diagram planar. -/
theorem Planar.subst {H : ∀ {a b : List Color}, Γ a b → Diagram Γ' a b}
    (hH : ∀ {a b : List Color} (g : Γ a b), (H g).Planar) {a b : List Color}
    {D : Diagram Γ a b} (hD : D.Planar) : (D.subst H).Planar := by
  induction D with
  | gen g => exact hH g
  | id _ => trivial
  | swap => exact hD.elim
  | comp _ _ ih₁ ih₂ => exact ⟨ih₁ hD.1, ih₂ hD.2⟩
  | tensor _ _ ih₁ ih₂ => exact ⟨ih₁ hD.1, ih₂ hD.2⟩

/-- **Substitution is an open simulation**, when each replacement implements its generator:
`OpenSim I I' (gen g) (H g)` for every generator `g`. -/
@[expose] def openSimSubst {H : ∀ {a b : List Color}, Γ a b → Diagram Γ' a b}
    (h : ∀ {a b : List Color} (g : Γ a b), OpenSim I I' (gen g) (H g)) :
    {a b : List Color} → (D : Diagram Γ a b) → OpenSim I I' D (D.subst H)
  | _, _, gen g => h g
  | _, _, id a => OpenSim.idWires a
  | _, _, swap x y => OpenSim.swapWires x y
  | _, _, comp D₁ D₂ => (openSimSubst h D₁).comp (openSimSubst h D₂)
  | _, _, tensor D₁ D₂ => (openSimSubst h D₁).tensor (openSimSubst h D₂)

/-- **An open simulation induces a simulation of constraint graphs**, for any boundary. -/
@[expose] def OpenSim.toSimulation {D : Diagram Γ a b} {D' : Diagram Γ' a b}
    (S : OpenSim I I' D D') : ConstraintGraph.Simulation (D.graph I) (D'.graph I') where
  abs t := t ∘ S.ι
  enc := S.enc
  abs_enc s := funext (S.enc_ι s)
  legal_abs := S.sound
  legal_enc := S.legal_enc
  step_abs := by
    rintro t t' ⟨ht, ht', y, rfl⟩
    by_cases hy : ∃ x, S.ι x = y
    · obtain ⟨x, rfl⟩ := hy
      exact .single ⟨S.sound ht, S.sound ht', x,
        reverse_comp_of_injective S.ι_injective t x⟩
    · rw [reverse_comp_of_not_mem_range t (fun x h => hy ⟨x, h⟩)]
  step_enc := by
    rintro s s' ⟨hs, hs', x, rfl⟩
    obtain ⟨u, hp, hf, hq⟩ := S.lift x hs hs'
    exact hp.reachable.trans (ReflTransGen.head ⟨InnerReach.legal hp (S.legal_enc hs), hf, _, rfl⟩
      hq.reachable)

/-- **Substitution preserves and reflects reachability**: a simulation of the graph of a
diagram by the graph of its substitution, for any boundary. -/
@[expose] def substSimulation {H : ∀ {a b : List Color}, Γ a b → Diagram Γ' a b}
    (h : ∀ {a b : List Color} (g : Γ a b), OpenSim I I' (gen g) (H g)) (D : Diagram Γ a b) :
    ConstraintGraph.Simulation (D.graph I) ((D.subst H).graph I') :=
  (openSimSubst h D).toSimulation

end Cslib.Complexity.NCL.Diagram
