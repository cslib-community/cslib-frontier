/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Gadgets.Expansion
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Realization
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.TreeJunction

/-!
# Arbitrary-arity OR trees

An OR tree joins blue inputs by binary OR vertices, starting with a fixed blue endpoint.

## Main definitions

* `Cslib.Complexity.NCL.Gadgets.OrTree.bundle`: the input bundle.
* `Cslib.Complexity.NCL.Gadgets.OrTree.generator`: an arbitrary-arity OR constraint.

## Main results

* `Cslib.Complexity.NCL.Gadgets.OrTree.openSim`: exact arbitrary-arity OR implementation.
* `Cslib.Complexity.NCL.Gadgets.OrTree.length_vertexList`,
  `Cslib.Complexity.NCL.Gadgets.OrTree.innerCount`: linear size.

## References

* [E. D. Demaine and R. A. Hearn, *Constraint Logic: A Uniform Framework for Modeling
  Computation as Games*][DemaineHearn2008]
-/

public section

attribute [local implicit_reducible] Cslib.Complexity.NCL.Diagram.Inner
  Cslib.Complexity.NCL.Diagram.InnerStep Cslib.Complexity.NCL.Diagram.instDecidableEqInner

namespace Cslib.Complexity.NCL.Gadgets.OrTree

open Diagram
local notation "B" => Color.blue

/-- The blue input bundle, with one input added on the left at every stage. -/
abbrev bundle : ℕ → List Color
  | 0 => []
  | n + 1 => B :: bundle n

/-- A blue OR constraint of arbitrary arity, with its output below. -/
@[expose] def generator (n : ℕ) : Prim (bundle n) [B] :=
  [⟨(List.finRange (bundle n).length).map (fun i => ⟨⟨.inl i, true⟩, 2⟩) ++
    [⟨⟨.inr 0, false⟩, 2⟩], 2⟩]

/-- The single-vertex drawing of the OR constraint. -/
abbrev node (n : ℕ) : Diagram Prim (bundle n) [B] := gen (generator n)

/-- Split off the first input using a binary OR vertex. -/
abbrev grow (n : ℕ) : Diagram Prim (bundle (n + 1)) [B] :=
  ((Diagram.id [B]).tensor (node n)).comp (gen [genVertex [B, B] [B] 2])

/-- The AND/OR tree, starting with the three-AND fixed endpoint. -/
@[expose] def diagram : (n : ℕ) → Diagram Prim (bundle n) [B]
  | 0 => Gadgets.fixedBlue
  | n + 1 => ((Diagram.id [B]).tensor (diagram n)).comp
      (gen [genVertex [B, B] [B] 2])

/-- The first input of a grown tree. -/
private def first (n : ℕ) : Fin (bundle (n + 1)).length :=
  (List.appendIndexEquiv [B] (bundle n)) (.inl 0)

/-- An old input, after adding one input on the left. -/
private def rest (n : ℕ) (i : Fin (bundle n).length) : Fin (bundle (n + 1)).length :=
  (List.appendIndexEquiv [B] (bundle n)) (.inr i)

/-- The boundary and intermediate wires of one growing step. -/
private abbrev GrowEdge (n : ℕ) :=
  TreeJunction.Edge ([B] ++ bundle n).length

/-- The disjunction of the old input directions. -/
private def active (n : ℕ) (β : Fin (bundle (n + 1)).length ⊕ Fin 1 → Bool) : Bool :=
  decide (∃ i, β (.inl (rest n i)) = true)

/-- Canonical extension: the intermediate wire carries the disjunction of the old inputs. -/
private def canon (n : ℕ) (β : Fin (bundle (n + 1)).length ⊕ Fin 1 → Bool) : GrowEdge n → Bool :=
  TreeJunction.put β (active n β)

end Cslib.Complexity.NCL.Gadgets.OrTree

end

public section

attribute [local implicit_reducible] Cslib.Complexity.NCL.Diagram.Inner
  Cslib.Complexity.NCL.Diagram.InnerStep Cslib.Complexity.NCL.Diagram.instDecidableEqInner

namespace Cslib.Complexity.NCL.Gadgets.OrTree

open Diagram
local notation "B" => Color.blue

/-- The input bundle has one wire per input. -/
@[simp] theorem length_bundle : ∀ n, (bundle n).length = n
  | 0 => rfl
  | n + 1 => congrArg (· + 1) (length_bundle n)

/-- Every OR input wire is blue. -/
@[simp] theorem getElem_bundle : ∀ n (i : Fin (bundle n).length), (bundle n)[i.val] = B
  | 0, i => i.elim0
  | n + 1, i => Fin.cases rfl (fun j => getElem_bundle n j) i

private theorem uniform_or {E : Type*} (ps : List (Port E)) (s : E → Bool) :
    (⟨ps.map (fun p => ⟨p, 2⟩), 2⟩ : Vertex E).Sat s ↔ ∃ p ∈ ps, p.In s := by
  simp only [Vertex.Sat, Vertex.inflow, List.map_map, Function.comp_def]
  induction ps with
  | nil => simp
  | cons p ps ih => by_cases hp : p.In s <;> simp [hp, ih]

/-- An OR boundary is legal exactly when an input is inward or the output is inward. -/
theorem legal_generator_iff (n : ℕ) (β : Fin (bundle n).length ⊕ Fin 1 → Bool) :
    ((node n).graph Prim.interp).Legal β ↔
      (∃ i, β (.inl i) = true) ∨ β (.inr (0 : Fin 1)) = false := by
  change ((gen (generator n) : Diagram Prim (bundle n) [B]).graph Prim.interp).Legal β ↔ _
  rw [← genLegal_iff]
  change (∀ v ∈ generator n, v.Sat β) ↔ _
  have h := uniform_or
    ((List.finRange (bundle n).length).map (fun i => ⟨.inl i, true⟩) ++ [⟨.inr 0, false⟩]) β
  simp only [List.map_append, List.map_map, Function.comp_def, List.map_cons, List.map_nil] at h
  simp only [generator, List.mem_singleton, forall_eq, h]
  simp [Port.In]

private theorem input_cases (n : ℕ) (i : Fin (bundle (n + 1)).length) :
    i = first n ∨ ∃ j, i = rest n j := by
  let e := (List.appendIndexEquiv [B] (bundle n)).symm
  rcases hi : e i with j | j
  · exact Or.inl <| e.injective (by simp [first, e, hi, Fin.eq_zero j])
  · exact Or.inr ⟨j, e.injective (by simp [rest, e, hi])⟩

private theorem legal_grow_iff (n : ℕ) (s : GrowEdge n → Bool) :
    ((grow n).graph Prim.interp).Legal s ↔
      ((∃ i, s (.inl (rest n i)) = true) ∨ s (TreeJunction.middle) = false) ∧
      (s (.inl (first n)) = true ∨ s (TreeJunction.middle) = true ∨
        s ((grow n).bottom 0) = false) := by
  change ((((Diagram.id [B]).tensor (node n)).comp
    (gen [genVertex [B, B] [B] 2])).graph Prim.interp).Legal s ↔ _
  rw [legal_comp_iff, legal_tensor_iff, legal_generator_iff]
  simp only [legal_id, true_and]
  refine and_congr_right fun _ => ?_
  rw [← genLegal_iff]
  simp only [GenLegal, Prim.interp, List.mem_singleton, forall_eq]
  change (2 ≤ (if s (.inl (first n)) = true then 2 else 0) +
    ((if s TreeJunction.middle = true then 2 else 0) +
      ((if s ((grow n).bottom 0) = false then 2 else 0) + 0))) ↔ _
  cases s (.inl (first n)) <;> cases s TreeJunction.middle <;> cases s ((grow n).bottom 0) <;> simp

private theorem source_iff (n : ℕ)
    (β : Fin (bundle (n + 1)).length ⊕ Fin 1 → Bool) :
    ((node (n + 1)).graph Prim.interp).Legal β ↔
      β (.inl (first n)) = true ∨ active n β = true ∨ β (.inr 0) = false := by
  rw [legal_generator_iff]
  simp only [active, decide_eq_true_eq]
  refine ⟨?_, ?_⟩
  · rintro (⟨i, hi⟩ | ho)
    · exact (input_cases n i).elim (fun h => Or.inl (h ▸ hi))
        fun ⟨j, h⟩ => Or.inr (Or.inl ⟨j, h ▸ hi⟩)
    · exact Or.inr (Or.inr ho)
  · rintro (hi | ⟨i, hi⟩ | ho)
    · exact Or.inl ⟨first n, hi⟩
    · exact Or.inl ⟨rest n i, hi⟩
    · exact Or.inr ho

private theorem legal_put_iff (n : ℕ)
    (β : Fin (bundle (n + 1)).length ⊕ Fin 1 → Bool) (c : Bool) :
    ((grow n).graph Prim.interp).Legal (TreeJunction.put β c) ↔
      (active n β = true ∨ c = false) ∧
      (β (.inl (first n)) = true ∨ c = true ∨ β (.inr 0) = false) := by
  rw [legal_grow_iff]
  simp only [TreeJunction.put, TreeJunction.middle, bottom, active, decide_eq_true_eq]

private theorem legal_canon (n : ℕ)
    {β : Fin (bundle (n + 1)).length ⊕ Fin 1 → Bool}
    (hβ : ((node (n + 1)).graph Prim.interp).Legal β) :
    ((grow n).graph Prim.interp).Legal (canon n β) := by
  apply (legal_put_iff n β _).2
  exact ⟨by cases active n β <;> simp, (source_iff n β).1 hβ⟩

private theorem middle_inner (n : ℕ) : ¬(grow n).IsBoundary TreeJunction.middle := by
  rintro (⟨i, hi⟩ | ⟨i, hi⟩) <;> simp [TreeJunction.middle, grow, bottom] at hi

private theorem junction_bmap (n : ℕ) (x : Fin (bundle (n + 1)).length ⊕ Fin 1) :
    (grow n).bmap x = TreeJunction.boundary x := by cases x <;> rfl

private theorem active_mono (n : ℕ)
    {β γ : Fin (bundle (n + 1)).length ⊕ Fin 1 → Bool}
    (h : ∀ i, β (.inl i) ≤ γ (.inl i)) : active n β ≤ active n γ := by
  apply Bool.le_iff_imp.2
  intro hβ
  obtain ⟨i, hi⟩ := of_decide_eq_true hβ
  exact decide_eq_true ⟨i, Bool.eq_true_of_true_le (hi ▸ h (rest n i))⟩

private theorem active_eq (n : ℕ)
    {β γ : Fin (bundle (n + 1)).length ⊕ Fin 1 → Bool}
    (h : ∀ i, β (.inl i) = γ (.inl i)) : active n β = active n γ :=
  le_antisymm (active_mono n (fun i => (h i).le)) (active_mono n (fun i => (h i).ge))

private theorem positive_input_legal (n : ℕ)
    (β : Fin (bundle (n + 1)).length ⊕ Fin 1 → Bool)
    (i : Fin (bundle (n + 1)).length) (hx : β (.inl i) = false)
    (hβ : ((node (n + 1)).graph Prim.interp).Legal β) :
    ((grow n).graph Prim.interp).Legal
      (TreeJunction.put (reverse β (.inl i)) (active n β)) := by
  have ham := active_mono n (fun k => TreeJunction.le_reverse_of_false β (.inl i) hx (.inl k))
  refine (legal_put_iff n _ _).mpr ⟨?_, ?_⟩
  · cases ha : active n β
    · exact Or.inr rfl
    · exact Or.inl (Bool.eq_true_of_true_le (ha ▸ ham))
  · rcases (source_iff n β).mp hβ with h | h | h
    · exact Or.inl (Bool.eq_true_of_true_le
        (h ▸ TreeJunction.le_reverse_of_false β (.inl i) hx (.inl (first n))))
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ((reverse_of_ne β (by simp)).trans h))

private def growOpenSim (n : ℕ) : OpenSim Prim.interp Prim.interp (node (n + 1)) (grow n) where
  ι := (grow n).bmap
  ι_injective := by
    rintro (i | i) (j | j) h <;>
      simp only [bmap, Sum.elim_inl, Sum.elim_inr, grow, bottom] at h <;> cases h <;> rfl
  ι_top _ := rfl
  ι_bottom _ := rfl
  enc := canon n
  enc_ι β x := by
    rw [junction_bmap]
    exact TreeJunction.put_boundary β _ x
  sound {t} ht := by
    apply (source_iff n _).2
    obtain ⟨hc, hj⟩ := (legal_grow_iff n t).1 ht
    rcases hj with h | h | h
    · exact Or.inl h
    · right; left
      simp only [active, decide_eq_true_eq]
      rcases hc with ⟨i, hi⟩ | hc
      · exact ⟨i, hi⟩
      · simp only [h, Bool.true_eq_false] at hc
    · exact Or.inr (Or.inr h)
  legal_enc hβ := legal_canon n hβ
  lift x hs ht := OpenSim.lift_of_false (D := node (n + 1)) (D' := grow n)
    (grow n).bmap (canon n) (fun h => legal_canon n h)
    (TreeJunction.positive_lift ((grow n).graph Prim.interp)
      (fun y => ¬(grow n).IsBoundary y) (middle_inner n) (grow n).bmap
      (fun β => ((node (n + 1)).graph Prim.interp).Legal β) (active n)
      (fun β c x => by rw [junction_bmap]; exact TreeJunction.reverse_boundary β c x)
      (fun β h => legal_canon n h) (positive_input_legal n)
      (fun β j => active_eq n (fun i => (reverse_of_ne β (by simp)).symm))) x hs ht

private def baseOpenSim : OpenSim Prim.interp Prim.interp (node 0) Gadgets.fixedBlue :=
  (OpenSim.genOfVerts (I := Prim.interp) (I' := Gate.interp)
    (generator 0) (Gate.vert 2) rfl).trans Gadgets.FixedBlue.openSim

/-- An arbitrary-arity OR is implemented by a linear-size tree of standard AND/OR cells. -/
def openSim : (n : ℕ) → OpenSim Prim.interp Prim.interp (node n) (diagram n)
  | 0 => baseOpenSim
  | n + 1 => (growOpenSim n).trans
      (((OpenSim.idWires [B]).tensor (openSim n)).comp (OpenSim.refl _))

/-- Every vertex of the implementation is a standard single-vertex AND/OR cell. -/
theorem checkStandard : ∀ n, (diagram n).checkGens
    (fun g => (g.length == 1) && Prim.checkStandard g) = true
  | 0 => by decide +kernel
  | n + 1 => by
    change (true && (diagram n).checkGens _) && true = true
    simp [checkStandard n]

/-- The OR tree has no crossings. -/
theorem planar : ∀ n, (diagram n).Planar
  | 0 => by decide +kernel
  | n + 1 => ⟨⟨True.intro, planar n⟩, True.intro⟩

/-- Each input adds one OR vertex to the three-AND endpoint. -/
theorem length_vertexList : ∀ n, ((diagram n).vertexList Prim.interp).length = n + 3
  | 0 => by decide +kernel
  | n + 1 => by
    simpa [diagram, vertexList, Prim.interp, Nat.add_assoc, Nat.add_right_comm] using
      length_vertexList n

/-- Each input adds one created wire to the endpoint's five wires. -/
theorem innerCount : ∀ n, (diagram n).innerCount = n + 5
  | 0 => by decide +kernel
  | n + 1 => by
    change 0 + (diagram n).innerCount + 1 = n + 1 + 5
    rw [innerCount n]; omega

end Cslib.Complexity.NCL.Gadgets.OrTree
