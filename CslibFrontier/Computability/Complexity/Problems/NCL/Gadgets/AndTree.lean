/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Gadgets.AndTree.Cell
public import CslibFrontier.Computability.Complexity.Problems.NCL.Gadgets.OrTree

/-!
# Arbitrary-arity conjunction trees with blue boundaries

The output may point outward only when every input points inward. A free source supplies the
empty conjunction, and each additional input is joined by the blue conjunction cell.

## Main definitions

* `Gadgets.AndTree.generator`: the shared-output conjunction clauses.
* `Gadgets.AndTree.diagram`: the recursively composed standard implementation.

## Main results

* `Gadgets.AndTree.openSim`: exact open simulation at every arity.
* `Gadgets.AndTree.length_vertexList`, `Gadgets.AndTree.innerCount`: linear size bounds.
-/

public section

attribute [local implicit_reducible] Cslib.Complexity.NCL.Diagram.Inner
  Cslib.Complexity.NCL.Diagram.InnerStep Cslib.Complexity.NCL.Diagram.instDecidableEqInner

namespace Cslib.Complexity.NCL.Gadgets.AndTree

open Diagram
local notation "B" => Color.blue

/-- Each input supplies one implication to the shared blue output. -/
@[expose] def generator (n : ℕ) : Prim (OrTree.bundle n) [B] :=
  (List.finRange (OrTree.bundle n).length).map fun i =>
    Vertex.clause [⟨.inl i, true⟩, ⟨.inr 0, false⟩]

private abbrev node (n : ℕ) : Diagram Prim (OrTree.bundle n) [B] := gen (generator n)

private abbrev grow (n : ℕ) : Diagram Prim (OrTree.bundle (n + 1)) [B] :=
  ((Diagram.id [B]).tensor (node n)).comp (gen binaryGenerator)

/-- A free blue source followed by one conjunction cell per input. -/
@[expose] def diagram : (n : ℕ) → Diagram Prim (OrTree.bundle n) [B]
  | 0 => Gadgets.freeStart
  | n + 1 => ((Diagram.id [B]).tensor (diagram n)).comp binaryDiagram

private def first (n : ℕ) : Fin (OrTree.bundle (n + 1)).length := 0

private def rest (n : ℕ) (i : Fin (OrTree.bundle n).length) :
    Fin (OrTree.bundle (n + 1)).length := i.succ

private def active (n : ℕ) (β : Fin (OrTree.bundle (n + 1)).length ⊕ Fin 1 → Bool) : Bool :=
  decide (∀ i, β (.inl (rest n i)) = true)

private def canon (n : ℕ) (β : Fin (OrTree.bundle (n + 1)).length ⊕ Fin 1 → Bool) :
    (grow n).Edge → Bool := TreeJunction.put β (active n β)

/-- The source requires all inputs precisely when its output points outward. -/
theorem legal_generator_iff (n : ℕ) (β : Fin (OrTree.bundle n).length ⊕ Fin 1 → Bool) :
    (((gen (generator n) : Diagram Prim (OrTree.bundle n) [B])).graph Prim.interp).Legal β ↔
      (∀ i, β (.inl i) = true) ∨ β (.inr 0) = false := by
  rw [← genLegal_iff]
  by_cases ho : β (.inr 0) = false <;>
    simp [GenLegal, Prim.interp, generator, Vertex.sat_clause_iff, Port.In, ho]

private theorem legal_grow_iff (n : ℕ) (s : (grow n).Edge → Bool) :
    ((grow n).graph Prim.interp).Legal s ↔
      ((∀ i, s (.inl (rest n i)) = true) ∨ s (TreeJunction.middle) = false) ∧
      (s ((grow n).bottom 0) = false ∨
        s (.inl (first n)) = true ∧ s (TreeJunction.middle) = true) := by
  rw [legal_comp_iff, legal_tensor_iff]
  simp only [legal_id, true_and]
  rw [legal_generator_iff, legal_binary_iff]
  have hfirst : List.appendIndexEquiv [B] (OrTree.bundle n) (.inl 0) = first n := by
    apply Fin.ext
    exact List.val_appendIndexEquiv_inl [B] (OrTree.bundle n) 0
  have hrest (i : Fin (OrTree.bundle n).length) :
      List.appendIndexEquiv [B] (OrTree.bundle n) (.inr i) = rest n i := by
    apply Fin.ext
    exact (List.val_appendIndexEquiv_inr [B] (OrTree.bundle n) i).trans (Nat.add_comm 1 i.val)
  change (((∀ i, s (.inl (List.appendIndexEquiv [B] (OrTree.bundle n) (.inr i))) = true) ∨
      s (TreeJunction.middle) = false) ∧
      (s ((grow n).bottom 0) = false ∨
        s (.inl (List.appendIndexEquiv [B] (OrTree.bundle n) (.inl 0))) = true ∧
          s (TreeJunction.middle) = true)) ↔ _
  simp only [hfirst, hrest]

private theorem source_iff (n : ℕ)
    (β : Fin (OrTree.bundle (n + 1)).length ⊕ Fin 1 → Bool) :
    ((node (n + 1)).graph Prim.interp).Legal β ↔
      β (.inr 0) = false ∨ β (.inl (first n)) = true ∧ active n β = true := by
  rw [legal_generator_iff]
  rw [show active n β = true ↔ ∀ i, β (.inl (rest n i)) = true from
    Iff.of_eq decide_eq_true_eq]
  change ((∀ i : Fin ((OrTree.bundle n).length + 1), β (.inl i) = true) ∨
    β (.inr 0) = false) ↔
      (β (.inr 0) = false ∨ β (.inl 0) = true ∧
        ∀ i : Fin (OrTree.bundle n).length, β (.inl i.succ) = true)
  rw [Fin.forall_fin_succ]
  exact or_comm

private theorem legal_put_iff (n : ℕ)
    (β : Fin (OrTree.bundle (n + 1)).length ⊕ Fin 1 → Bool) (c : Bool) :
    ((grow n).graph Prim.interp).Legal (TreeJunction.put β c) ↔
      (active n β = true ∨ c = false) ∧
      (β (.inr 0) = false ∨ β (.inl (first n)) = true ∧ c = true) := by
  rw [legal_grow_iff]
  simp only [TreeJunction.put, TreeJunction.middle, bottom, active, decide_eq_true_eq]

private theorem legal_canon (n : ℕ)
    {β : Fin (OrTree.bundle (n + 1)).length ⊕ Fin 1 → Bool}
    (hβ : ((node (n + 1)).graph Prim.interp).Legal β) :
    ((grow n).graph Prim.interp).Legal (canon n β) := by
  apply (legal_put_iff n β _).mpr
  exact ⟨by cases active n β <;> simp, (source_iff n β).mp hβ⟩

private theorem middle_inner (n : ℕ) : ¬(grow n).IsBoundary TreeJunction.middle := by
  rintro (⟨i, hi⟩ | ⟨i, hi⟩) <;> simp [TreeJunction.middle, grow, bottom] at hi

private theorem junction_bmap (n : ℕ)
    (x : Fin (OrTree.bundle (n + 1)).length ⊕ Fin 1) :
    (grow n).bmap x = TreeJunction.boundary x := by cases x <;> rfl

private theorem active_mono (n : ℕ)
    {β γ : Fin (OrTree.bundle (n + 1)).length ⊕ Fin 1 → Bool}
    (h : ∀ i, β (.inl i) ≤ γ (.inl i)) : active n β ≤ active n γ := by
  apply Bool.le_iff_imp.mpr
  intro hβ
  apply decide_eq_true
  intro i
  exact Bool.eq_true_of_true_le ((of_decide_eq_true hβ i) ▸ h (rest n i))

private theorem active_eq (n : ℕ)
    {β γ : Fin (OrTree.bundle (n + 1)).length ⊕ Fin 1 → Bool}
    (h : ∀ i, β (.inl i) = γ (.inl i)) : active n β = active n γ :=
  le_antisymm (active_mono n (fun i => (h i).le)) (active_mono n (fun i => (h i).ge))

private theorem positive_input_legal (n : ℕ)
    (β : Fin (OrTree.bundle (n + 1)).length ⊕ Fin 1 → Bool)
    (i : Fin (OrTree.bundle (n + 1)).length) (hx : β (.inl i) = false)
    (hβ : ((node (n + 1)).graph Prim.interp).Legal β) :
    ((grow n).graph Prim.interp).Legal
      (TreeJunction.put (reverse β (.inl i)) (active n β)) := by
  have ham := active_mono n (β := β) (γ := reverse β (.inl i))
    (fun k => TreeJunction.le_reverse_of_false β (.inl i) hx (.inl k))
  apply (legal_put_iff n _ _).mpr
  constructor
  · cases ha : active n β
    · exact Or.inr rfl
    · exact Or.inl (Bool.eq_true_of_true_le (ha ▸ ham))
  · rcases (source_iff n β).mp hβ with ho | ⟨hf, hc⟩
    · exact Or.inl ((reverse_of_ne β (by simp)).trans ho)
    · exact Or.inr ⟨Bool.eq_true_of_true_le
        (hf ▸ TreeJunction.le_reverse_of_false β (.inl i) hx (.inl (first n))), hc⟩

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
    apply (source_iff n _).mpr
    obtain ⟨hc, hj⟩ := (legal_grow_iff n t).mp ht
    rcases hj with ho | ⟨hf, hm⟩
    · exact Or.inl ho
    · refine Or.inr ⟨hf, ?_⟩
      apply decide_eq_true
      rcases hc with hc | hc
      · exact hc
      · exact Bool.noConfusion (hm.symm.trans hc)
  legal_enc hβ := legal_canon n hβ
  lift x hs ht := OpenSim.lift_of_false (D := node (n + 1)) (D' := grow n)
    (grow n).bmap (canon n) (fun h => legal_canon n h)
    (TreeJunction.positive_lift ((grow n).graph Prim.interp)
      (fun y => ¬(grow n).IsBoundary y) (middle_inner n) (grow n).bmap
      (fun β => ((node (n + 1)).graph Prim.interp).Legal β) (active n)
      (fun β c x => by rw [junction_bmap]; exact TreeJunction.reverse_boundary β c x)
      (fun β h => legal_canon n h) (positive_input_legal n)
      (fun β j => active_eq n (fun i => (reverse_of_ne β (by simp)).symm))) x hs ht

private def baseCert : Cert (generator 0) Gadgets.freeStart where
  canon := Gadgets.FreeStart.cert.canon
  rounds := Gadgets.FreeStart.cert.rounds
  refute := Gadgets.FreeStart.cert.refute
  pre := Gadgets.FreeStart.cert.pre
  post := Gadgets.FreeStart.cert.post

private def baseOpenSim : OpenSim Prim.interp Prim.interp (node 0) Gadgets.freeStart :=
  OpenSim.ofCert baseCert (by decide +kernel)

/-- Every arity is implemented by a tree of ordinary AND/OR cells with blue boundary ports. -/
def openSim : (n : ℕ) → OpenSim Prim.interp Prim.interp (gen (generator n)) (diagram n)
  | 0 => baseOpenSim
  | n + 1 => (growOpenSim n).trans
      (((OpenSim.idWires [B]).tensor (openSim n)).comp binaryOpenSim)

/-- Every generator of the implementation is a standard AND/OR cell. -/
theorem checkStandard : ∀ n, (diagram n).checkGens Prim.checkStandard = true
  | 0 => by decide +kernel
  | n + 1 => by
    change (true && (diagram n).checkGens Prim.checkStandard) &&
      binaryDiagram.checkGens Prim.checkStandard = true
    rw [checkStandard n, binary_checkStandard]
    rfl

/-- Each additional input contributes fifteen standard vertices. -/
theorem length_vertexList : ∀ n, ((diagram n).vertexList Prim.interp).length = 15 * n + 3
  | 0 => by decide +kernel
  | n + 1 => by
    simp only [diagram, vertexList, List.length_append, List.length_map,
      List.length_nil, Nat.zero_add]
    rw [length_vertexList n, binary_vertexCount]
    omega

/-- Each additional input contributes twenty-two created wires. -/
theorem innerCount : ∀ n, (diagram n).innerCount = 22 * n + 5
  | 0 => by decide +kernel
  | n + 1 => by
    change 0 + (diagram n).innerCount + binaryDiagram.innerCount = _
    rw [innerCount n, binary_innerCount]
    omega

end Cslib.Complexity.NCL.Gadgets.AndTree
