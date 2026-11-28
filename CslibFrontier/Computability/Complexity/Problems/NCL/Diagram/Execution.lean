/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Realization
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Activation

/-!
# Composing executions across shared wires

Selected-edge paths can change a shared boundary. To lift such a path, the surrounding part
must remain legal and follow the shared reversal. Preparing a quantifier changes the inputs of
an inactive suffix; executing that suffix changes only its satisfied input, which the prepared
quantifier follows. These two operations compose the protocols of [HearnDemaine2005, Lemma 3].

## Main definitions

* `Cslib.Complexity.NCL.Diagram.AllowsTop`: reversal edges fixing every input except one.
* `Cslib.Complexity.NCL.Diagram.glueResponse`: attach a component whose configuration depends
  on one input direction of its suffix.

## Main results

* `Cslib.Complexity.NCL.Diagram.reachableOn_glueResponse`: lift a suffix call and its response.
* `Cslib.Complexity.NCL.Diagram.reachableOn_glueResponse_allowsTop`: calls using `AllowsTop`.
* `Cslib.Complexity.NCL.Diagram.reachableOn_compAssoc`: transfer paths across regrouping.
* `Cslib.Complexity.NCL.Diagram.Realization.withTop`: give an inactive closed component more
  incoming support while retaining all created wires.

## References

* [R. A. Hearn and E. D. Demaine, *PSPACE-completeness of sliding-block puzzles and other
  problems through the nondeterministic constraint logic model of computation*][HearnDemaine2005]
-/

public section

namespace Cslib.Complexity.NCL.Diagram

variable {Γ : List Color → List Color → Type} {I : Interp Γ} {a b c d : List Color}

/-- Allowed reversal edges when only input `j` may change. Created edges remain unrestricted. -/
@[expose] def AllowsTop {n : ℕ} {E : Type} (j : ℕ) (e : Fin n ⊕ E) : Prop :=
  ∀ i, i.val ≠ j → e ≠ .inl i

@[simp] theorem allowsTop_inl {n : ℕ} {E : Type} (j : ℕ) (i : Fin n) :
    AllowsTop j (.inl i : Fin n ⊕ E) ↔ i.val = j :=
  ⟨fun h => Decidable.byContradiction fun hi => h i hi rfl,
    fun hi _ hk he => hk ((congrArg Fin.val (Sum.inl.inj he)).symm.trans hi)⟩

@[simp] theorem allowsTop_inr {n : ℕ} {E : Type} (j : ℕ) (e : E) :
    AllowsTop j (.inr e : Fin n ⊕ E) := fun _ _ => nofun

private theorem allowsTop_symm_apply {E E' : Type} {n : ℕ}
    (σ : (Fin n ⊕ E) ≃ (Fin n ⊕ E'))
    (hσ : ∀ i, σ (.inl i) = .inl i) (j : ℕ) (e : Fin n ⊕ E') :
    AllowsTop j (σ.symm e) ↔ AllowsTop j e := by
  simp only [AllowsTop, ne_eq, Equiv.symm_apply_eq, hσ]

/-- Read the first incoming direction separately from the remaining inputs. -/
theorem topList_cons {color : Color} (D : Diagram Γ (color :: a) b) (s : D.Edge → Bool) :
    D.topList s = s (.inl ⟨0, Nat.zero_lt_succ _⟩) :: (D.topList s).tail := by
  simp [topList, List.ofFn_succ]

/-- A call changing only its first input retains all remaining incoming directions. -/
theorem topList_of_reachableOn {color : Color} {D : Diagram Γ (color :: a) b}
    {s t : D.Edge → Bool} {bit : Bool} {xs : List Bool}
    (h : (D.graph I).ReachableOn (AllowsTop 0) s t)
    (hs : D.topList s = bit :: xs) :
    D.topList t = t (.inl ⟨0, Nat.zero_lt_succ _⟩) :: xs := by
  have htail : (D.topList t).tail = (D.topList s).tail := by
    simp only [topList, List.ofFn_succ, List.tail_cons, List.ofFn_inj]
    exact funext fun i => (h.apply_eq fun hall => hall i.succ (by simp) rfl).symm
  rw [topList_cons D t, htail, hs]; rfl

/-- Remove a leading identity diagram from the edge names of a stack. -/
@[expose] def idComp (D : Diagram Γ a b) : ((Diagram.id a).comp D).Edge ≃ D.Edge :=
  Equiv.sumCongr (Equiv.refl _) (Equiv.emptySum Empty D.Inner)

/-- Removing a leading identity preserves legality. -/
theorem legal_idComp (D : Diagram Γ a b) (s : D.Edge → Bool) :
    (((Diagram.id a).comp D).graph I).Legal (s ∘ idComp D) ↔ (D.graph I).Legal s := by
  have he : (s ∘ idComp D) ∘ compRight (Diagram.id a) D = s := funext fun | .inl _ | .inr _ => rfl
  simp only [legal_comp_iff, legal_id, true_and, he]

/-- Lift a selected-edge path through a leading identity diagram. -/
theorem reachableOn_idComp (D : Diagram Γ a b) {s t : D.Edge → Bool}
    {allowed : D.Edge → Prop} {allowed' : ((Diagram.id a).comp D).Edge → Prop}
    (h : (D.graph I).ReachableOn allowed s t) (hs : (D.graph I).Legal s)
    (he : ∀ e, allowed e → allowed' ((idComp D).symm e)) :
    (((Diagram.id a).comp D).graph I).ReachableOn allowed'
      (s ∘ idComp D) (t ∘ idComp D) :=
  h.map (· ∘ idComp D) (idComp D).symm
    (fun u hu => (legal_idComp D u).2 (hu.reachable.legal hs))
    (fun u e _ => reverse_comp_equiv (idComp D) u e) he

/-- Adding leading identity wires preserves the permitted changing input. -/
theorem reachableOn_idComp_allowsTop (D : Diagram Γ a b) (j : ℕ)
    {s t : D.Edge → Bool} (h : (D.graph I).ReachableOn (AllowsTop j) s t)
    (hs : (D.graph I).Legal s) :
    (((Diagram.id a).comp D).graph I).ReachableOn (AllowsTop j)
      (s ∘ idComp D) (t ∘ idComp D) :=
  reachableOn_idComp D h hs fun e he =>
    (allowsTop_symm_apply (idComp D) (fun _ => rfl) j e).2 he

/-- A relation on the input lists holds on each incoming wire. -/
theorem rel_of_forall₂_topList {D : Diagram Γ a b} {s t : D.Edge → Bool}
    {R : Bool → Bool → Prop} (h : List.Forall₂ R (D.topList s) (D.topList t))
    (i : Fin a.length) : R (s (.inl i)) (t (.inl i)) := by
  unfold topList at h
  have hi := h.get (by simpa only [List.length_ofFn] using i.isLt)
    (by simpa only [List.length_ofFn] using i.isLt)
  simpa only [List.get_ofFn, Function.comp_apply, Fin.cast_mk, Fin.eta] using hi

/-- Increase the incoming directions of a closed forward component, retaining its created
wires. This changes the inputs of an inactive suffix without running that suffix. -/
@[expose] def Realization.withTop {D : Diagram Γ a []} {x : List Bool}
    (s : Realization I D x []) (hI : I.Forward) (x' : List Bool)
    (hlen : x'.length = a.length) (hle : List.Forall₂ (· ≤ ·) x x') :
    Realization I D x' [] :=
  let wires := Realization.id (I := I) a x' hlen
  { orient := Sum.elim (fun i => wires.orient (.inl i)) (fun e => s.orient (.inr e))
    legal := by
      refine legal_top_mono hI D s.legal ?_ (fun _ => rfl)
      have hb : List.Forall₂ (· ≤ ·) (D.topList s.orient) (D.topList
          (Sum.elim (fun i => wires.orient (.inl i)) (fun e => s.orient (.inr e)))) := by
        change List.Forall₂ (· ≤ ·) (D.topList s.orient) ((Diagram.id a).topList wires.orient)
        rw [s.top_eq, wires.top_eq]
        exact hle
      exact rel_of_forall₂_topList hb
    top_eq := wires.top_eq
    bot_eq := rfl }

/-- Regroup three stacked diagrams, keeping their incoming wires and all created wires. -/
@[expose] def compAssoc (D₁ : Diagram Γ a b) (D₂ : Diagram Γ b c) (D₃ : Diagram Γ c d) :
    ((D₁.comp D₂).comp D₃).Edge ≃ (D₁.comp (D₂.comp D₃)).Edge :=
  Equiv.sumCongr (Equiv.refl _) (Equiv.sumAssoc _ _ _)

/-- Regrouping a stack preserves every inflow constraint. -/
theorem legal_compAssoc (D₁ : Diagram Γ a b) (D₂ : Diagram Γ b c) (D₃ : Diagram Γ c d)
    (s : (D₁.comp (D₂.comp D₃)).Edge → Bool) :
    (((D₁.comp D₂).comp D₃).graph I).Legal (s ∘ compAssoc D₁ D₂ D₃) ↔
      ((D₁.comp (D₂.comp D₃)).graph I).Legal s := by
  have h₁ : ((s ∘ compAssoc D₁ D₂ D₃) ∘ compLeft (D₁.comp D₂) D₃) ∘ compLeft D₁ D₂ =
      s ∘ compLeft D₁ (D₂.comp D₃) := funext fun | .inl _ | .inr _ => rfl
  have h₂ : ((s ∘ compAssoc D₁ D₂ D₃) ∘ compLeft (D₁.comp D₂) D₃) ∘ compRight D₁ D₂ =
      (s ∘ compRight D₁ (D₂.comp D₃)) ∘ compLeft D₂ D₃ := funext fun
    | .inl i => by
      cases hi : D₁.bottom i <;> simp only [Function.comp_apply, compRight, compLeft,
        Sum.map, Sum.elim_inl, Sum.elim_inr, id_eq, hi] <;> rfl
    | .inr _ => rfl
  have h₃ : (s ∘ compAssoc D₁ D₂ D₃) ∘ compRight (D₁.comp D₂) D₃ =
      (s ∘ compRight D₁ (D₂.comp D₃)) ∘ compRight D₂ D₃ := funext fun
    | .inl i => by
      simp only [Function.comp_apply, compRight, bottom_comp]
      rcases D₂.bottom i with j | _
      · cases hj : D₁.bottom j <;> simp only [compLeft, Sum.map, Sum.elim_inl, Sum.elim_inr,
          Function.comp_apply, id_eq, hj] <;> rfl
      · rfl
    | .inr _ => rfl
  simp only [legal_comp_iff, h₁, h₂, h₃, and_assoc]

/-- A selected-edge execution transfers across regrouping. -/
theorem reachableOn_compAssoc (D₁ : Diagram Γ a b) (D₂ : Diagram Γ b c) (D₃ : Diagram Γ c d)
    {s t : (D₁.comp (D₂.comp D₃)).Edge → Bool}
    {allowed : (D₁.comp (D₂.comp D₃)).Edge → Prop}
    {allowed' : ((D₁.comp D₂).comp D₃).Edge → Prop}
    (h : ((D₁.comp (D₂.comp D₃)).graph I).ReachableOn allowed s t)
    (hs : ((D₁.comp (D₂.comp D₃)).graph I).Legal s)
    (he : ∀ e, allowed e → allowed' ((compAssoc D₁ D₂ D₃).symm e)) :
    (((D₁.comp D₂).comp D₃).graph I).ReachableOn allowed'
      (s ∘ compAssoc D₁ D₂ D₃) (t ∘ compAssoc D₁ D₂ D₃) :=
  h.map (· ∘ compAssoc D₁ D₂ D₃) (compAssoc D₁ D₂ D₃).symm
    (fun u hu => (legal_compAssoc D₁ D₂ D₃ u).2 (hu.reachable.legal hs))
    (fun u e _ => reverse_comp_equiv (compAssoc D₁ D₂ D₃) u e) he

/-- Regrouping a stack preserves the permitted changing input. -/
theorem reachableOn_compAssoc_allowsTop (D₁ : Diagram Γ a b) (D₂ : Diagram Γ b c)
    (D₃ : Diagram Γ c d) (j : ℕ)
    {s t : (D₁.comp (D₂.comp D₃)).Edge → Bool}
    (h : ((D₁.comp (D₂.comp D₃)).graph I).ReachableOn (AllowsTop j) s t)
    (hs : ((D₁.comp (D₂.comp D₃)).graph I).Legal s) :
    (((D₁.comp D₂).comp D₃).graph I).ReachableOn (AllowsTop j)
      (s ∘ compAssoc D₁ D₂ D₃) (t ∘ compAssoc D₁ D₂ D₃) :=
  reachableOn_compAssoc D₁ D₂ D₃ h hs fun e he =>
    (allowsTop_symm_apply (compAssoc D₁ D₂ D₃) (fun _ => rfl) j e).2 he

/-- Attach a component whose orientation follows one incoming direction of its suffix. -/
@[expose] def glueResponse (D₁ : Diagram Γ a b) (D₂ : Diagram Γ b c)
    (j : Fin b.length) (f : Bool → D₁.Edge → Bool) (u : D₂.Edge → Bool) :
    (D₁.comp D₂).Edge → Bool := glueComp D₁ D₂ (f (u (.inl j))) u

private theorem glueResponse_reverse {D₁ : Diagram Γ a b} {D₂ : Diagram Γ b c}
    (j : Fin b.length) (f : Bool → D₁.Edge → Bool)
    (hf : f false = reverse (f true) (D₁.bottom j)) (u : D₂.Edge → Bool) (e : D₂.Edge)
    (he : ∀ i, i ≠ j → e ≠ .inl i) :
    glueResponse D₁ D₂ j f (reverse u e) =
      reverse (glueResponse D₁ D₂ j f u) (compRight D₁ D₂ e) := by
  rcases e with i | e
  · obtain rfl : i = j := Decidable.byContradiction fun hne => he i hne rfl
    have hflip (b : Bool) : f (!b) = reverse (f b) (D₁.bottom i) := by
      cases b <;> simp [hf, reverse_reverse]
    simp only [glueResponse, reverse_self, hflip]
    exact (glueComp_congr_right D₁ D₂ _ fun _ => reverse_of_ne u (by simp)).trans
      (glueComp_reverse_left D₁ D₂ _ u _)
  · simp only [glueResponse, reverse_of_ne u (show (.inl j : D₂.Edge) ≠ .inr e by simp)]
    exact glueComp_reverse_right D₁ D₂ _ u e

/-- Lift a suffix execution that fixes every input except `j`. Its attached component follows
that direction by reversing the matching output wire. The legality hypothesis is checked only
at states reached by the suffix path, so it also supports calls with a retained record. -/
theorem reachableOn_glueResponse {D₁ : Diagram Γ a b} {D₂ : Diagram Γ b c}
    (j : Fin b.length) (f : Bool → D₁.Edge → Bool)
    (hf : f false = reverse (f true) (D₁.bottom j)) {s t : D₂.Edge → Bool}
    (h : (D₂.graph I).ReachableOn (fun e => ∀ i, i ≠ j → e ≠ .inl i) s t)
    {allowed : (D₁.comp D₂).Edge → Prop}
    (hlegal : ∀ u, (D₂.graph I).ReachableOn (fun e => ∀ i, i ≠ j → e ≠ .inl i) s u →
      ((D₁.comp D₂).graph I).Legal (glueResponse D₁ D₂ j f u))
    (hallowed : ∀ e, (∀ i, i ≠ j → e ≠ .inl i) → allowed (compRight D₁ D₂ e)) :
    ((D₁.comp D₂).graph I).ReachableOn allowed
      (glueResponse D₁ D₂ j f s) (glueResponse D₁ D₂ j f t) :=
  h.map (glueResponse D₁ D₂ j f) (compRight D₁ D₂) hlegal
    (glueResponse_reverse j f hf) hallowed

/-- Lift a suffix call whose allowed reversal edges are expressed by their input number. -/
theorem reachableOn_glueResponse_allowsTop {D₁ : Diagram Γ a b} {D₂ : Diagram Γ b c}
    (j : Fin b.length) (f : Bool → D₁.Edge → Bool)
    (hf : f false = reverse (f true) (D₁.bottom j)) {s t : D₂.Edge → Bool}
    (h : (D₂.graph I).ReachableOn (AllowsTop j) s t)
    {allowed : (D₁.comp D₂).Edge → Prop}
    (hlegal : ∀ u, (D₂.graph I).ReachableOn (AllowsTop j) s u →
      ((D₁.comp D₂).graph I).Legal (glueResponse D₁ D₂ j f u))
    (hallowed : ∀ e, AllowsTop j e → allowed (compRight D₁ D₂ e)) :
    ((D₁.comp D₂).graph I).ReachableOn allowed
      (glueResponse D₁ D₂ j f s) (glueResponse D₁ D₂ j f t) := by
  have he : (AllowsTop (j : ℕ) : D₂.Edge → Prop) = fun e => ∀ i, i ≠ j → e ≠ .inl i :=
    funext fun _ => by simp only [AllowsTop, ne_eq, Fin.ext_iff]
  rw [he] at h hlegal hallowed
  exact reachableOn_glueResponse j f hf h hlegal hallowed

end Cslib.Complexity.NCL.Diagram
