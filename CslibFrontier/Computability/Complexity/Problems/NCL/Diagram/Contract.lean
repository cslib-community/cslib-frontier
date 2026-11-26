/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Implements

/-!
# Static contracts of diagrams

A static contract of a diagram (`Cslib.Complexity.NCL.Diagram.Holds`) is a relation between the
directions of its top wires and those of its bottom wires, as lists, that every legal
configuration satisfies. Contracts compose: a stack satisfies the relational composite of the
contracts of its parts, and a juxtaposition their product. So the static behaviour of a large,
parametric diagram, such as a network that evaluates a formula, follows from the contracts of
its few kinds of small gadgets, and each of these is checked once on its boundary
(`Cslib.Complexity.NCL.Diagram.Holds.of_check`): every boundary configuration either satisfies
the contract or is refuted.

## Main definitions

* `Cslib.Complexity.NCL.Diagram.topList`, `Cslib.Complexity.NCL.Diagram.botList`: the directions
  of the wires above and below.
* `Cslib.Complexity.NCL.Diagram.Holds`: a static contract.

## Main results

* `Cslib.Complexity.NCL.Diagram.Holds.comp`, `Cslib.Complexity.NCL.Diagram.Holds.tensor`,
  `Cslib.Complexity.NCL.Diagram.Holds.id`, `Cslib.Complexity.NCL.Diagram.Holds.swap`: contracts
  compose.
* `Cslib.Complexity.NCL.Diagram.Holds.of_check`: the contract of a gadget, checked on its
  boundary.
* `Cslib.Complexity.NCL.Diagram.topList_compRight`,
  `Cslib.Complexity.NCL.Diagram.botList_tensor`: wire readings commute with composition.
* `Cslib.Complexity.NCL.Diagram.Holds.moveLeft`: routing a wire across a bundle preserves
  directions and reorders the boundary lists.

## References

* The NCL application follows [Hearn and Demaine][HearnDemaine2005].
-/

public section

namespace Cslib.Complexity.NCL.Diagram

variable {Γ : List Color → List Color → Type} {I : Interp Γ} {a b c d : List Color} {Label : Type*}

/-- The values on the top wires. -/
@[expose] def topList (D : Diagram Γ a b) (t : D.Edge → Label) : List Label := List.ofFn (t ∘ .inl)

/-- The values on the bottom wires. -/
@[expose]
def botList (D : Diagram Γ a b) (t : D.Edge → Label) : List Label := List.ofFn (t ∘ D.bottom)

@[simp] theorem length_topList (D : Diagram Γ a b) (t : D.Edge → Label) :
    (D.topList t).length = a.length :=
  List.length_ofFn

@[simp] theorem length_botList (D : Diagram Γ a b) (t : D.Edge → Label) :
    (D.botList t).length = b.length :=
  List.length_ofFn

/-- The top wires of the upper part are the top wires of the stack. -/
theorem topList_compLeft (D₁ : Diagram Γ a b) (D₂ : Diagram Γ b c)
    (t : (D₁.comp D₂).Edge → Label) :
    D₁.topList (t ∘ compLeft D₁ D₂) = (D₁.comp D₂).topList t := rfl

/-- The shared wires are read identically from either part of a stack. -/
theorem topList_compRight (D₁ : Diagram Γ a b) (D₂ : Diagram Γ b c)
    (t : (D₁.comp D₂).Edge → Label) :
    D₂.topList (t ∘ compRight D₁ D₂) = D₁.botList (t ∘ compLeft D₁ D₂) := rfl

/-- The bottom wires of the lower part are the bottom wires of the stack. -/
theorem botList_compRight (D₁ : Diagram Γ a b) (D₂ : Diagram Γ b c)
    (t : (D₁.comp D₂).Edge → Label) :
    D₂.botList (t ∘ compRight D₁ D₂) = (D₁.comp D₂).botList t :=
  List.ofFn_inj.2 (funext fun j => by simp [bottom_comp])

/-- Reading the top wires of a juxtaposition concatenates the readings of its parts. -/
theorem topList_tensor (D₁ : Diagram Γ a b) (D₂ : Diagram Γ c d)
    (t : (D₁.tensor D₂).Edge → Label) :
    (D₁.tensor D₂).topList t = D₁.topList (t ∘ tensorLeft D₁ D₂) ++
      D₂.topList (t ∘ tensorRight D₁ D₂) := List.ofFn_appendIndexEquiv a c _

/-- Reading the bottom wires of a juxtaposition concatenates the readings of its parts. -/
theorem botList_tensor (D₁ : Diagram Γ a b) (D₂ : Diagram Γ c d)
    (t : (D₁.tensor D₂).Edge → Label) :
    (D₁.tensor D₂).botList t = D₁.botList (t ∘ tensorLeft D₁ D₂) ++
      D₂.botList (t ∘ tensorRight D₁ D₂) :=
  (List.ofFn_appendIndexEquiv b d _).trans (congrArg₂ (· ++ ·)
    (List.ofFn_inj.2 (funext fun j => by simp [bottom_tensor_left]))
    (List.ofFn_inj.2 (funext fun j => by simp [bottom_tensor_right])))

variable (I) in
/-- **A static contract**: every legal configuration of `D` relates the directions of its top
wires and of its bottom wires by `C`. -/
@[expose]
def Holds (D : Diagram Γ a b) (C : List Bool → List Bool → Prop) : Prop :=
  ∀ t, (D.graph I).Legal t → C (D.topList t) (D.botList t)

namespace Holds

theorem mono {D : Diagram Γ a b} {C C' : List Bool → List Bool → Prop} (h : Holds I D C)
    (hC : ∀ x y, x.length = a.length → y.length = b.length → C x y → C' x y) : Holds I D C' :=
  fun t ht => hC _ _ (length_topList ..) (length_botList ..) (h t ht)

/-- **A stack satisfies the composite of the contracts of its parts.** -/
theorem comp {D₁ : Diagram Γ a b} {D₂ : Diagram Γ b c} {C₁ C₂ : List Bool → List Bool → Prop}
    (h₁ : Holds I D₁ C₁) (h₂ : Holds I D₂ C₂) :
    Holds I (D₁.comp D₂) fun x z => ∃ y, C₁ x y ∧ C₂ y z := fun t ht => by
  obtain ⟨ht₁, ht₂⟩ := (legal_comp_iff D₁ D₂ t).1 ht
  exact ⟨_, h₁ _ ht₁, by simpa only [botList_compRight, topList_compRight] using h₂ _ ht₂⟩

/-- **A juxtaposition satisfies the product of the contracts of its parts.** -/
theorem tensor {D₁ : Diagram Γ a b} {D₂ : Diagram Γ c d} {C₁ C₂ : List Bool → List Bool → Prop}
    (h₁ : Holds I D₁ C₁) (h₂ : Holds I D₂ C₂) :
    Holds I (D₁.tensor D₂) fun x y => ∃ x₁ x₂ y₁ y₂, x = x₁ ++ x₂ ∧ y = y₁ ++ y₂ ∧
      x₁.length = a.length ∧ y₁.length = b.length ∧ C₁ x₁ y₁ ∧ C₂ x₂ y₂ := fun t ht => by
  obtain ⟨ht₁, ht₂⟩ := (legal_tensor_iff D₁ D₂ t).1 ht
  exact ⟨_, _, _, _, topList_tensor D₁ D₂ t, botList_tensor D₁ D₂ t,
    List.length_ofFn, List.length_ofFn, h₁ _ ht₁, h₂ _ ht₂⟩

/-- Wires running straight down keep their directions. -/
theorem id (a : List Color) : Holds I (Diagram.id a : Diagram Γ a a) (· = ·) := fun _ _ => rfl

/-- Crossing wires exchange their directions. -/
theorem swap (x y : Color) :
    Holds I (Diagram.swap x y : Diagram Γ [x, y] [y, x]) fun u v => v = u.reverse :=
  fun _ _ => rfl

/-- A diagram beside wires on its left. -/
theorem id_tensor (l : List Color) {D : Diagram Γ a b} {C : List Bool → List Bool → Prop}
    (h : Holds I D C) :
    Holds I ((Diagram.id l).tensor D) fun x y => ∃ z x' y', x = z ++ x' ∧ y = z ++ y' ∧
      z.length = l.length ∧ C x' y' :=
  ((id l).tensor h).mono <| by
    rintro _ _ - - ⟨z, x', _, y', rfl, rfl, hz, -, rfl, hC⟩
    exact ⟨z, x', y', rfl, rfl, hz, hC⟩

/-- A diagram beside wires on its right. -/
theorem tensor_id (r : List Color) {D : Diagram Γ a b} {C : List Bool → List Bool → Prop}
    (h : Holds I D C) :
    Holds I (D.tensor (Diagram.id r)) fun x y => ∃ x' y' z, x = x' ++ z ∧ y = y' ++ z ∧
      x'.length = a.length ∧ y'.length = b.length ∧ C x' y' :=
  (h.tensor (id r)).mono <| by
    rintro _ _ - - ⟨x', z, y', _, rfl, rfl, hx', hy', hC, rfl⟩
    exact ⟨x', y', z, rfl, rfl, hx', hy', hC⟩

/-- Moving one wire left across a bundle preserves every direction and reorders the lists. -/
theorem moveLeft : ∀ (l : List Color) (x : Color) (r : List Color),
    Holds I (Diagram.moveLeft l x r : Diagram Γ _ _) fun u v =>
      ∃ us bit rs, u = us ++ bit :: rs ∧ v = bit :: (us ++ rs) ∧
        us.length = l.length ∧ rs.length = r.length
  | [], x, r => (id _).mono <| by
    rintro u _ hu - rfl
    obtain ⟨bit, rs, rfl⟩ := List.exists_cons_of_length_eq_add_one hu
    exact ⟨[], bit, rs, rfl, rfl, rfl, by simpa using hu⟩
  | y :: l, x, r => (((moveLeft l x r).id_tensor [y]).comp
      ((swap y x).tensor_id (l ++ r))).mono <| by
    rintro _ _ - - ⟨_, ⟨z, _, _, rfl, rfl, hz, us, bit, rs, rfl, rfl, hus, hrs⟩,
      ⟨u, _, tail, hmid, rfl, hu, -, rfl⟩⟩
    obtain ⟨first, rfl⟩ := List.length_eq_one_iff.1 hz
    obtain ⟨a, b, rfl⟩ := List.length_eq_two.1 hu
    obtain ⟨rfl, rfl, rfl⟩ : first = a ∧ bit = b ∧ us ++ rs = tail := by simpa using hmid
    exact ⟨_ :: us, _, rs, rfl, rfl, by simp [hus], hrs⟩

end Holds

/-- The partial orientation fixing the top wires to `x` and the bottom wires to `y`. -/
@[expose] def boundaryOf (D : Diagram Γ a b) (x y : List Bool) : List (D.Edge × Bool) :=
  (List.finRange a.length).map (fun i : Fin a.length => (.inl i, x.getD i false)) ++
    (List.finRange b.length).map (fun j : Fin b.length => (D.bottom j, y.getD j false))

/-- The lists of directions of `n` wires. -/
@[expose] def allLists : ℕ → List (List Bool)
  | 0 => [[]]
  | n + 1 => (allLists n).flatMap fun l => [false :: l, true :: l]

private theorem mem_allLists : ∀ {n : ℕ} {l : List Bool}, l.length = n → l ∈ allLists n
  | 0, [], _ => List.mem_singleton_self _
  | n + 1, x :: l, h =>
    List.mem_flatMap.2 ⟨l, mem_allLists (Nat.succ_injective h), by cases x <;> simp⟩

/-- **The contract of a gadget, checked on its boundary**: every boundary configuration either
satisfies the contract or is refuted by `n` rounds of propagation. -/
theorem Holds.of_check {D : Diagram Γ a b} {C : List Bool → List Bool → Prop} (n : ℕ)
    (h : ∀ x ∈ allLists a.length, ∀ y ∈ allLists b.length, C x y ∨
      Refutation.conflict.check (numVertexList I D) n (D.numOrient (D.boundaryOf x y)) = true) :
    Holds I D C := fun t ht => by
  refine (h _ (mem_allLists (length_topList ..)) _ (mem_allLists (length_botList ..))).resolve_right
    fun hr => not_extends_of_refutes ((Refutation.conflict).refutes hr) ht fun p hp => ?_
  simp only [boundaryOf, List.mem_append, List.mem_map, List.mem_finRange, true_and] at hp
  rcases hp with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp [topList, botList]

end Cslib.Complexity.NCL.Diagram
