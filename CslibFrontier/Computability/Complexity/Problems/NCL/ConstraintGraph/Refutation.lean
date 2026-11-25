/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Basic
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.Group.Nat

/-!
# Refutations by unit propagation

To show that no orientation extending a partial one satisfies a list of vertices, it suffices to
give a refutation (`Cslib.Complexity.NCL.Refutation`): the edges on which to split into cases.
Between splits, unit propagation does the rest
(`Cslib.Complexity.NCL.propagateRounds`). Since every constraint is monotone, propagation is sound:

* if a vertex is not satisfied even when every undetermined edge points into it, there is no
  extension at all;
* if a vertex is not satisfied unless some undetermined edge points into it, every satisfying
  extension has that edge pointing into it.

A refutation is checked by a function (`Cslib.Complexity.NCL.Refutation.check`) that visits
the vertices for a fixed number of propagation rounds at each node. Its cost also includes
lookups in the partial orientation; its correctness is proved once
(`Cslib.Complexity.NCL.Refutation.refutes`). A refutation is essentially a proof such as
that of [HearnDemaine2005, Lemma 7]: "suppose `A` faces up; without loss of generality `E` faces
left; then `F`, `G` and `H` face left, …".

## Main definitions

* `Cslib.Complexity.NCL.Extends`: a full orientation extends a partial one.
* `Cslib.Complexity.NCL.propagateRounds`: rounds of unit propagation.
* `Cslib.Complexity.NCL.Refutes`: no extension of a partial orientation satisfies the vertices.
* `Cslib.Complexity.NCL.Refutation`, `Cslib.Complexity.NCL.Refutation.check`: refutations and
  their checker.

## Main results

* `Cslib.Complexity.NCL.Refutation.refutes`: a checked refutation refutes.
* `Cslib.Complexity.NCL.Refutes.not_step`: refuting the vertices before and after a reversal rules
  out the move.
* `Cslib.Complexity.NCL.Refutes.of_map`: refutations survive injective renaming of the edges.

## References

* [R. A. Hearn and E. D. Demaine, *PSPACE-completeness of sliding-block puzzles and other
  problems through the nondeterministic constraint logic model of computation*][HearnDemaine2005]
-/

public section

namespace Cslib.Complexity.NCL

variable {E : Type*}

/-- The full orientation `t` agrees with every entry of the partial orientation `ρ`, a list of
edges with directions. -/
@[expose] def Extends (t : E → Bool) (ρ : List (E × Bool)) : Prop := ∀ p ∈ ρ, t p.1 = p.2

/-- No extension of the partial orientation `ρ` satisfies every vertex of `vs`. -/
@[expose] def Refutes (vs : List (Vertex E)) (ρ : List (E × Bool)) : Prop :=
  ∀ ⦃t : E → Bool⦄, Extends t ρ → ¬∀ v ∈ vs, v.Sat t

@[simp] theorem extends_nil (t : E → Bool) : Extends t [] := fun _ h => absurd h List.not_mem_nil

@[simp] theorem extends_cons {t : E → Bool} {p : E × Bool} {ρ : List (E × Bool)} :
    Extends t (p :: ρ) ↔ t p.1 = p.2 ∧ Extends t ρ :=
  List.forall_mem_cons

private theorem Extends.cons {t : E → Bool} {ρ : List (E × Bool)}
    (h : Extends t ρ) {e : E} {b : Bool}
    (he : t e = b) : Extends t ((e, b) :: ρ) :=
  List.forall_mem_cons.2 ⟨he, h⟩

namespace Vertex

private theorem sum_add_le_of_mem {α : Type*} {l : List α} {f g : α → ℕ} {x : α} (hx : x ∈ l)
    (hfx : f x = 0) (h : ∀ y ∈ l, f y ≤ g y) : (l.map f).sum + g x ≤ (l.map g).sum := by
  induction l with
  | nil => exact absurd hx List.not_mem_nil
  | cons y l ih =>
    simp only [List.map_cons, List.sum_cons]
    rcases eq_or_ne x y with rfl | hxy
    · have := List.sum_le_sum (l := l) fun z hz => h z (List.mem_cons_of_mem _ hz)
      omega
    · have := ih (List.mem_of_ne_of_mem hxy hx) fun z hz => h z (List.mem_cons_of_mem _ hz)
      have := h y List.mem_cons_self
      omega

end Vertex

section Propagation

variable [DecidableEq E]

private theorem Extends.lookup {t : E → Bool} {ρ : List (E × Bool)}
    (h : Extends t ρ) {e : E} {b : Bool}
    (he : ρ.lookup e = some b) : t e = b := by
  obtain ⟨l₁, l₂, rfl, _⟩ := List.lookup_eq_some_iff.1 he
  exact h (e, b) (List.mem_append_right _ List.mem_cons_self)

namespace Port

/-- Under the partial orientation `ρ`, the edge may still point into this endpoint. -/
@[expose] def mayIn (p : Port E) (ρ : List (E × Bool)) : Bool :=
  match ρ.lookup p.edge with
  | none => true
  | some b => b == p.dir

private theorem mayIn_of_in {p : Port E} {t : E → Bool} {ρ : List (E × Bool)} (h : Extends t ρ)
    (hp : p.In t) : p.mayIn ρ = true := by
  unfold mayIn
  rcases hρ : ρ.lookup p.edge with _ | b
  · rfl
  · rw [← h.lookup hρ]
    exact beq_iff_eq.2 hp

/-- The port with its direction reversed if it is on the edge `e`. -/
@[expose] def flipAt (e : E) (p : Port E) : Port E :=
  ⟨p.edge, if p.edge = e then !p.dir else p.dir⟩

theorem in_flipAt (e : E) (p : Port E) (t : E → Bool) :
    (p.flipAt e).In t ↔ p.In (reverse t e) := by
  unfold flipAt In
  by_cases h : p.edge = e
  · subst h
    simp only [↓reduceIte, reverse_self]
    cases t p.edge <;> cases p.dir <;> decide
  · simp [h, reverse_of_ne t h]

end Port

namespace Vertex

/-- An upper bound on the in-flow under `ρ`, allowing every undetermined port to point in. -/
@[expose] def maxInflow (v : Vertex E) (ρ : List (E × Bool)) : ℕ :=
  (v.ports.map fun p => if p.port.mayIn ρ then p.weight else 0).sum

/-- An extension receives at most the largest in-flow. -/
private theorem inflow_le_maxInflow (v : Vertex E) {t : E → Bool} {ρ : List (E × Bool)}
    (h : Extends t ρ) : v.inflow t ≤ v.maxInflow ρ :=
  List.sum_le_sum fun p _ => by by_cases hp : p.port.In t <;> simp [hp, Port.mayIn_of_in h]

/-- An extension in which the undetermined edge of the port `p` points away receives at most the
largest in-flow less the weight of `p`. -/
private theorem inflow_add_le_maxInflow (v : Vertex E) {t : E → Bool} {ρ : List (E × Bool)}
    (h : Extends t ρ) {p : WeightedPort E} (hp : p ∈ v.ports) (hρ : ρ.lookup p.port.edge = none)
    (ht : ¬p.port.In t) : v.inflow t + p.weight ≤ v.maxInflow ρ := by
  have hsum := sum_add_le_of_mem (f := fun p => if p.port.In t then p.weight else 0)
    (g := fun p => if p.port.mayIn ρ then p.weight else 0) hp (by simp [ht]) fun q _ => by
      by_cases hq : q.port.In t <;> simp [hq, Port.mayIn_of_in h]
  simp only [show p.port.mayIn ρ = true by simp [Port.mayIn, hρ], ↓reduceIte] at hsum
  exact hsum

/-- The vertex seen after reversing the edge `e`. -/
@[expose] def flipAt (e : E) (v : Vertex E) : Vertex E :=
  ⟨v.ports.map fun p => ⟨p.port.flipAt e, p.weight⟩, v.minInflow⟩

theorem sat_flipAt (e : E) (v : Vertex E) (t : E → Bool) :
    (v.flipAt e).Sat t ↔ v.Sat (reverse t e) := by
  simp only [Sat, flipAt, inflow, List.map_map, Function.comp_def, Port.in_flipAt]

/-- The edges that the vertex forces under `ρ`, given its largest in-flow `m`, added to `ρ'`.
Reverse port order agrees with successive insertion at the head of the partial orientation. -/
@[expose] def force (v : Vertex E) (ρ : List (E × Bool)) (m : ℕ) (ρ' : List (E × Bool)) :
    List (E × Bool) :=
  (v.ports.filterMap fun p =>
    if ρ.lookup p.port.edge = none ∧ m < v.minInflow + p.weight then
      some (p.port.edge, p.port.dir) else none).reverse ++ ρ'

/-- Propagate one vertex: `none` if it cannot be satisfied any more; otherwise direct into it
every undetermined edge without which it cannot be satisfied. -/
@[expose] def propagate (v : Vertex E) (ρ : List (E × Bool)) : Option (List (E × Bool)) :=
  if v.maxInflow ρ < v.minInflow then none else some (v.force ρ (v.maxInflow ρ) ρ)

/-- **Propagation is sound**: a satisfying extension extends the result. -/
private theorem propagate_sound (v : Vertex E) {t : E → Bool} {ρ : List (E × Bool)}
    (h : Extends t ρ) (hv : v.Sat t) : ∃ ρ', v.propagate ρ = some ρ' ∧ Extends t ρ' := by
  have hmax := v.inflow_le_maxInflow h
  have hsat : v.minInflow ≤ v.inflow t := hv
  have hnot : ¬v.maxInflow ρ < v.minInflow := by omega
  simp only [propagate, hnot, ↓reduceIte, Option.some.injEq, exists_eq_left', force]
  intro p hp
  rcases List.mem_append.1 hp with hp | hp
  · obtain ⟨q, hq, hforce⟩ := List.mem_filterMap.1 (List.mem_reverse.1 hp)
    obtain ⟨hreq, heq⟩ := Option.ite_none_right_eq_some.1 hforce
    obtain rfl := Option.some.inj heq
    by_contra hout
    have := v.inflow_add_le_maxInflow h hq hreq.1 hout
    omega
  · exact h p hp

end Vertex

/-- One round of propagation through a list of vertices. -/
@[expose]
def propagateRound (vs : List (Vertex E)) (ρ : List (E × Bool)) : Option (List (E × Bool)) :=
  vs.foldlM (fun ρ v => v.propagate ρ) ρ

/-- `n` rounds of propagation: `none` once some vertex cannot be satisfied. -/
@[expose]
def propagateRounds (vs : List (Vertex E)) : ℕ → List (E × Bool) → Option (List (E × Bool))
  | 0, ρ => some ρ
  | n + 1, ρ => (propagateRound vs ρ).bind (propagateRounds vs n)

private theorem propagateRound_sound {vs : List (Vertex E)} {t : E → Bool}
    (hvs : ∀ v ∈ vs, v.Sat t) :
    ∀ {ρ : List (E × Bool)}, Extends t ρ →
      ∃ ρ', propagateRound vs ρ = some ρ' ∧ Extends t ρ' := by
  induction vs with
  | nil => exact fun h => ⟨_, rfl, h⟩
  | cons v vs ih =>
    intro ρ h
    obtain ⟨ρ₁, h₁, he₁⟩ := v.propagate_sound h (hvs v List.mem_cons_self)
    obtain ⟨ρ₂, h₂, he₂⟩ := ih (fun w hw => hvs w (List.mem_cons_of_mem _ hw)) he₁
    exact ⟨ρ₂, by simpa [propagateRound, h₁] using h₂, he₂⟩

/-- **Propagation is sound**: an extension satisfying every vertex extends the result. -/
private theorem propagateRounds_sound {vs : List (Vertex E)} {t : E → Bool}
    (hvs : ∀ v ∈ vs, v.Sat t) :
    ∀ (n : ℕ) {ρ : List (E × Bool)}, Extends t ρ →
      ∃ ρ', propagateRounds vs n ρ = some ρ' ∧ Extends t ρ'
  | 0, _, h => ⟨_, rfl, h⟩
  | n + 1, _, h => by
    obtain ⟨ρ₁, h₁, he₁⟩ := propagateRound_sound hvs h
    obtain ⟨ρ₂, h₂, he₂⟩ := propagateRounds_sound hvs n he₁
    exact ⟨ρ₂, by simp only [propagateRounds, h₁, Option.bind_some, h₂], he₂⟩

/-- A refutation: the edges on which to split into cases. Every leaf is closed by propagation. -/
inductive Refutation (E : Type*)
  /-- Propagation alone reaches a contradiction. -/
  | conflict
  /-- After propagation, split on the edge `e`: first `e = true`, then `e = false`. -/
  | split (e : E) (pos neg : Refutation E)

namespace Refutation

/-- Check a refutation, with `n` rounds of propagation before each split and at each leaf. -/
@[expose] def check (vs : List (Vertex E)) (n : ℕ) : Refutation E → List (E × Bool) → Bool
  | conflict, ρ => (propagateRounds vs n ρ).isNone
  | split e r₁ r₂, ρ =>
    match propagateRounds vs n ρ with
    | none => true
    | some ρ' => check vs n r₁ ((e, true) :: ρ') && check vs n r₂ ((e, false) :: ρ')

/-- **A checked refutation is correct.** -/
theorem refutes {vs : List (Vertex E)} {n : ℕ} :
    ∀ (r : Refutation E) {ρ : List (E × Bool)}, r.check vs n ρ = true → Refutes vs ρ
  | conflict, ρ, hr, t, h, hvs => by
    obtain ⟨ρ', hρ', -⟩ := propagateRounds_sound hvs n h
    simp [check, hρ'] at hr
  | split e r₁ r₂, ρ, hr, t, h, hvs => by
    obtain ⟨ρ', hρ', he⟩ := propagateRounds_sound hvs n h
    simp only [check, hρ', Bool.and_eq_true] at hr
    cases ht : t e
    · exact refutes r₂ hr.2 (he.cons ht) hvs
    · exact refutes r₁ hr.1 (he.cons ht) hvs

end Refutation

/-- **A refuted move never happens**: if `ρ` is refuted for the vertices together with the
vertices seen after reversing `e`, then no `t` extending `ρ` that satisfies the vertices before and
after the reversal exists. -/
theorem Refutes.not_step {vs : List (Vertex E)} {e : E} {ρ : List (E × Bool)}
    (hr : Refutes (vs ++ vs.map (Vertex.flipAt e)) ρ) {t : E → Bool} (h : Extends t ρ)
    (ht : ∀ v ∈ vs, v.Sat t) (ht' : ∀ v ∈ vs, v.Sat (reverse t e)) : False :=
  hr h <| List.forall_mem_append.2 ⟨ht, List.forall_mem_map.2 fun w hw =>
    (Vertex.sat_flipAt e w t).2 (ht' w hw)⟩

end Propagation

variable {E' : Type*} {f : E → E'}

private theorem sat_extend (hf : Function.Injective f) (t : E → Bool) (v : Vertex E) :
    (v.map f).Sat (Function.extend f t fun _ => false) ↔ v.Sat t := by
  rw [Vertex.sat_map]
  exact iff_of_eq (congrArg v.Sat (funext fun e => hf.extend_apply _ _ e))

private theorem extends_map (hf : Function.Injective f) {t : E → Bool} {l : List (E × Bool)}
    (h : Extends t l) :
    Extends (Function.extend f t fun _ => false) (l.map fun p => (f p.1, p.2)) :=
  List.forall_mem_map.2 fun q hq => (hf.extend_apply _ _ _).trans (h q hq)

/-- **Refutations survive renaming**: refuting the vertices over an injective renaming of the
edges, for instance by numbers, refutes them over the edges themselves. -/
theorem Refutes.of_map (hf : Function.Injective f) {vs : List (Vertex E)} {l : List (E × Bool)}
    (hr : Refutes (vs.map (Vertex.map f)) (l.map fun p => (f p.1, p.2))) : Refutes vs l :=
  fun t h hvs => hr (extends_map hf h) <|
    List.forall_mem_map.2 fun w hw => (sat_extend hf t w).2 (hvs w hw)

/-- Reversing an edge commutes with an injective renaming. -/
theorem Vertex.map_flipAt [DecidableEq E] [DecidableEq E'] (hf : Function.Injective f) (e : E)
    (v : Vertex E) : (v.flipAt e).map f = (v.map f).flipAt (f e) := by
  simp [Vertex.flipAt, Vertex.map, WeightedPort.map, Port.flipAt, Port.map, hf.eq_iff]

end Cslib.Complexity.NCL
