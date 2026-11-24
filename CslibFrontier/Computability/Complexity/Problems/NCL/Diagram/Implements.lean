/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Substitution
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Enumeration
public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.Refutation
public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.Run
public import Mathlib.Data.Fintype.Pi

/-!
# Implementing a generator by certificates

A diagram `H` implements a generator `g` with the same boundary when there is an open simulation
`OpenSim I I' (gen g) H`. For a concrete gadget, every obligation is a finite check, and
`Cslib.Complexity.NCL.Diagram.OpenSim.ofCert` turns certificates into such a simulation:

* the canonical inner configuration for each configuration of the boundary;
* for each boundary configuration that the generator forbids, a refutation
  (`Cslib.Complexity.NCL.Refutation`) showing that no configuration of `H` has it: this is the
  static soundness of [HearnDemaine2005, Lemmas 7 and 8];
* for each allowed reversal of a boundary wire, the moves inside `H` before and after it.

The certificates are checked by functions whose correctness is proved once; what remains to run
by `decide` quantifies only over the configurations and wires of the boundary.

## Main definitions

* `Cslib.Complexity.NCL.Diagram.InnerRun`, `Cslib.Complexity.NCL.Diagram.MoveCert`: checkable
  sequences of moves inside a diagram.
* `Cslib.Complexity.NCL.Diagram.Cert`, `Cslib.Complexity.NCL.Diagram.Cert.Valid`: certificates
  for an implementation, and their validity, decidable once and for all.
* `Cslib.Complexity.NCL.Diagram.Cert.movesOfForward`: complete a table from one move direction.
* `Cslib.Complexity.NCL.Diagram.OpenSim.ofCert`: an open simulation of a generator from valid
  certificates.

## Main results

* `Cslib.Complexity.NCL.Diagram.eq_of_refutes`,
  `Cslib.Complexity.NCL.Diagram.eq_of_refutes_step`: static properties of a diagram, and of its
  moves, from refutations, possibly under assumptions.

## References

* [R. A. Hearn and E. D. Demaine, *PSPACE-completeness of sliding-block puzzles and other
  problems through the nondeterministic constraint logic model of computation*][HearnDemaine2005]
-/

public section

namespace Cslib.Complexity.NCL

namespace Diagram

variable {Γ Γ' : List Color → List Color → Type} {I : Interp Γ} {I' : Interp Γ'}
  {a b : List Color}

/-- The wires of the boundary as edges: those above, then those below. -/
@[expose] def bmap (D : Diagram Γ a b) : Fin a.length ⊕ Fin b.length → D.Edge :=
  Sum.elim .inl D.bottom

instance (D : Diagram Γ a b) (y : D.Edge) : Decidable (D.IsBoundary y) :=
  inferInstanceAs (Decidable ((∃ i, y = .inl i) ∨ ∃ j, y = D.bottom j))

variable (I) in
/-- Every listed reversal is a move inside the diagram. -/
abbrev InnerRun (D : Diagram Γ a b) : (D.Edge → Bool) → List D.Edge → Prop :=
  (D.graph I).Run (fun e => ¬D.IsBoundary e)

theorem InnerRun.innerReach {D : Diagram Γ a b} :
    ∀ {t : D.Edge → Bool} {ys : List D.Edge}, InnerRun I D t ys →
      InnerReach I D t (reverseAll t ys) := fun h => h.reachableOn

variable (I) in
/-- A certificate for one move of an implementation: from `s`, the moves `pre` inside, the
reversal of `y`, then the moves `post` inside, ending at `s'`. -/
@[expose]
def MoveCert (D : Diagram Γ a b) (s : D.Edge → Bool) (pre : List D.Edge) (y : D.Edge)
    (post : List D.Edge) (s' : D.Edge → Bool) : Prop :=
  InnerRun I D s pre ∧ (D.graph I).Legal (reverse (reverseAll s pre) y) ∧
    InnerRun I D (reverse (reverseAll s pre) y) post ∧
      reverseAll (reverse (reverseAll s pre) y) post = s'

instance (D : Diagram Γ a b) (s : D.Edge → Bool) (pre : List D.Edge) (y : D.Edge)
    (post : List D.Edge) (s' : D.Edge → Bool) : Decidable (MoveCert I D s pre y post s') :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- The boundary points, listed. -/
@[expose] def boundaryList (a b : List Color) : List (Fin a.length ⊕ Fin b.length) :=
  (List.finRange a.length).map .inl ++ (List.finRange b.length).map .inr

/-- The partial orientation that fixes the boundary wires of `D` to `β` and nothing else. -/
@[expose] def boundaryPartial (D : Diagram Γ a b) (β : Fin a.length ⊕ Fin b.length → Bool) :
    List (D.Edge × Bool) :=
  (boundaryList a b).map fun x => (D.bmap x, β x)

theorem extends_boundaryPartial (D : Diagram Γ a b) (t : D.Edge → Bool) :
    Extends t (D.boundaryPartial (t ∘ D.bmap)) := fun p hp => by
  obtain ⟨x, -, rfl⟩ := List.mem_map.1 hp
  rfl

/-! ### Static properties by refutation -/

/-- The vertices of `D` on its numbered edges (`Cslib.Complexity.NCL.Diagram.num`). Refutations
are checked over these: comparing numbers is fast, also in the kernel. -/
@[expose] def numVertexList (I : Interp Γ) (D : Diagram Γ a b) : List (Vertex ℕ) :=
  (vertexList I D).map (Vertex.map D.num)

/-- The partial orientation of the numbered edges that fixes the listed edges. -/
@[expose] def numOrient (D : Diagram Γ a b) (l : List (D.Edge × Bool)) : List (ℕ × Bool) :=
  l.map fun p => (D.num p.1, p.2)

/-- **A refuted partial orientation never occurs under assumptions**: no legal configuration of
`D` satisfying the vertices `extra`, typically clauses, has the listed edges in the listed
directions. -/
theorem not_extends_of_refutes_assuming {D : Diagram Γ a b} {l : List (D.Edge × Bool)}
    (extra : List (Vertex D.Edge))
    (hr : Refutes (numVertexList I D ++ extra.map (Vertex.map D.num)) (D.numOrient l))
    {t : D.Edge → Bool} (ht : (D.graph I).Legal t) (hx : ∀ v ∈ extra, v.Sat t) :
    ¬Extends t l := fun h => by
  refine Refutes.of_map (vs := vertexList I D ++ extra) D.num_injective
    (by simpa only [numVertexList, numOrient, List.map_append] using hr) h fun v hv => ?_
  rcases List.mem_append.1 hv with hv | hv
  · exact (forall_vertexList_iff D t).2 ht v hv
  · exact hx v hv

/-- **A refuted partial orientation never occurs**: no legal configuration of `D` has the listed
edges in the listed directions. -/
theorem not_extends_of_refutes {D : Diagram Γ a b} {l : List (D.Edge × Bool)}
    (hr : Refutes (numVertexList I D) (D.numOrient l)) {t : D.Edge → Bool}
    (ht : (D.graph I).Legal t) : ¬Extends t l :=
  not_extends_of_refutes_assuming [] (by simpa using hr) ht (by simp)

/-- **A refuted move never happens under assumptions**: no legal configuration of `D` satisfying
the vertices `extra`, with the listed edges in the listed directions, can reverse `e`. -/
theorem not_extends_of_refutes_step_assuming {D : Diagram Γ a b} {e : D.Edge}
    {l : List (D.Edge × Bool)} (extra : List (Vertex D.Edge))
    (hr : Refutes (numVertexList I D ++ (numVertexList I D).map (Vertex.flipAt (D.num e)) ++
      extra.map (Vertex.map D.num)) (D.numOrient l))
    {t : D.Edge → Bool} (ht : (D.graph I).Legal t) (ht' : (D.graph I).Legal (reverse t e))
    (hx : ∀ v ∈ extra, v.Sat t) : ¬Extends t l :=
  -- the vertices seen after the reversal are constraints that `t` satisfies
  not_extends_of_refutes_assuming ((vertexList I D).map (Vertex.flipAt e) ++ extra)
    (by simpa only [numVertexList, List.map_append, List.map_map, Function.comp_def,
      Vertex.map_flipAt D.num_injective, List.append_assoc] using hr) ht fun v hv => by
    rcases List.mem_append.1 hv with hv | hv
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hv
      exact (Vertex.sat_flipAt e w t).2 ((forall_vertexList_iff D _).2 ht' w hw)
    · exact hx v hv

/-- **A refuted move never happens**: no legal configuration of `D` with the listed edges in the
listed directions can reverse `e`. -/
theorem not_extends_of_refutes_step {D : Diagram Γ a b} {e : D.Edge} {l : List (D.Edge × Bool)}
    (hr : Refutes (numVertexList I D ++ (numVertexList I D).map (Vertex.flipAt (D.num e)))
      (D.numOrient l))
    {t : D.Edge → Bool} (ht : (D.graph I).Legal t) (ht' : (D.graph I).Legal (reverse t e)) :
    ¬Extends t l := fun hl =>
  (Refutes.of_map D.num_injective
    (by simpa only [numVertexList, numOrient, List.map_append, List.map_map, Function.comp_def,
      Vertex.map_flipAt D.num_injective] using hr)).not_step hl
    ((forall_vertexList_iff D t).2 ht) ((forall_vertexList_iff D _).2 ht')

/-- **A static property of a diagram under assumptions, from a refutation of its negation**: in
every legal configuration satisfying the vertices `extra` (typically clauses) and extending `l`,
the edge `e` points as `c`. -/
theorem eq_of_refutes_assuming {D : Diagram Γ a b} {e : D.Edge} {c : Bool}
    {l : List (D.Edge × Bool)} (extra : List (Vertex D.Edge))
    (hr : Refutes (numVertexList I D ++ extra.map (Vertex.map D.num))
      (D.numOrient ((e, !c) :: l)))
    {t : D.Edge → Bool} (ht : (D.graph I).Legal t) (hx : ∀ v ∈ extra, v.Sat t)
    (hl : Extends t l) : t e = c :=
  by_contra fun h => not_extends_of_refutes_assuming extra hr ht hx
    (extends_cons.2 ⟨by cases c <;> simpa using h, hl⟩)

/-- **A static property of a diagram, from a refutation of its negation**: in every legal
configuration extending `l`, the edge `e` points as `c`. -/
theorem eq_of_refutes {D : Diagram Γ a b} {e : D.Edge} {c : Bool} {l : List (D.Edge × Bool)}
    (hr : Refutes (numVertexList I D) (D.numOrient ((e, !c) :: l)))
    {t : D.Edge → Bool} (ht : (D.graph I).Legal t) (hl : Extends t l) : t e = c :=
  eq_of_refutes_assuming [] (by simpa using hr) ht (by simp) hl

/-- **A static property of the moves of a diagram under assumptions, from a refutation of its
negation**: in every legal configuration satisfying the vertices `extra` and extending `l` from
which reversing `y` is a move, the edge `e` points as `c`. -/
theorem eq_of_refutes_step_assuming {D : Diagram Γ a b} {y e : D.Edge} {c : Bool}
    {l : List (D.Edge × Bool)} (extra : List (Vertex D.Edge))
    (hr : Refutes (numVertexList I D ++ (numVertexList I D).map (Vertex.flipAt (D.num y)) ++
      extra.map (Vertex.map D.num)) (D.numOrient ((e, !c) :: l)))
    {t : D.Edge → Bool} (ht : (D.graph I).Legal t) (ht' : (D.graph I).Legal (reverse t y))
    (hx : ∀ v ∈ extra, v.Sat t) (hl : Extends t l) : t e = c :=
  by_contra fun h => not_extends_of_refutes_step_assuming extra hr ht ht' hx
    (extends_cons.2 ⟨by cases c <;> simpa using h, hl⟩)

/-- **A static property of the moves of a diagram, from a refutation of its negation**: in every
legal configuration extending `l` from which reversing `y` is a move, the edge `e` points as
`c`. -/
theorem eq_of_refutes_step {D : Diagram Γ a b} {y e : D.Edge} {c : Bool}
    {l : List (D.Edge × Bool)}
    (hr : Refutes (numVertexList I D ++ (numVertexList I D).map (Vertex.flipAt (D.num y)))
      (D.numOrient ((e, !c) :: l)))
    {t : D.Edge → Bool} (ht : (D.graph I).Legal t) (ht' : (D.graph I).Legal (reverse t y))
    (hl : Extends t l) : t e = c :=
  by_contra fun h => not_extends_of_refutes_step hr ht ht'
    (extends_cons.2 ⟨by cases c <;> simpa using h, hl⟩)

/-- The boundary configurations that the generator `g` allows: its vertices are satisfied. -/
@[expose] def GenLegal (I : Interp Γ) (g : Γ a b) (β : Fin a.length ⊕ Fin b.length → Bool) : Prop :=
  ∀ v ∈ I.verts g, v.Sat β

instance (I : Interp Γ) (g : Γ a b) (β : Fin a.length ⊕ Fin b.length → Bool) :
    Decidable (GenLegal I g β) :=
  inferInstanceAs (Decidable (∀ v ∈ I.verts g, v.Sat β))

theorem genLegal_iff (g : Γ a b) (β : Fin a.length ⊕ Fin b.length → Bool) :
    GenLegal I g β ↔ ((gen g).graph I).Legal β :=
  forall_vertexList_iff (gen g) β

/-- The certificates for an implementation of the generator `g` by `H`. -/
structure Cert (g : Γ a b) (H : Diagram Γ' a b) where
  /-- The canonical configuration of `H` for each configuration of the boundary. -/
  canon : (Fin a.length ⊕ Fin b.length → Bool) → H.Edge → Bool
  /-- The rounds of propagation before each split of a refutation. -/
  rounds : ℕ
  /-- For each configuration of the boundary that `g` forbids, a refutation of it in `H`, on the
  numbered edges. -/
  refute : (Fin a.length ⊕ Fin b.length → Bool) → Refutation ℕ
  /-- The moves inside before reversing a wire of the boundary. -/
  pre : (Fin a.length ⊕ Fin b.length → Bool) → Fin a.length ⊕ Fin b.length → List H.Edge
  /-- The moves inside after reversing a wire of the boundary. -/
  post : (Fin a.length ⊕ Fin b.length → Bool) → Fin a.length ⊕ Fin b.length → List H.Edge

/-- Complete a numbered boundary-move table from its `false` to `true` entries. Bit `i` of
`code` is boundary direction `i`; reversing a move exchanges and reverses its two lists. -/
@[expose] def Cert.movesOfForward {E : Type} (forward : ℕ → ℕ → List E × List E) (code bit : ℕ) :
    List E × List E :=
  if code.testBit bit then
    let (pre, post) := forward (code - 2 ^ bit) bit
    (post.reverse, pre.reverse)
  else forward code bit

/-- A move certificate tabulated by boundary directions and creation-order edge numbers.
The low bits encode the top ports followed by the bottom ports, both from left to right.
Only forward moves are supplied. -/
structure Cert.Table (n : ℕ) where
  /-- Internal edges oriented forward in the canonical extension of this boundary. -/
  innerBits : ℕ → List ℕ
  /-- Propagation rounds between refutation splits. -/
  rounds : ℕ
  /-- Refutation tree for each forbidden boundary. -/
  refute : ℕ → Refutation ℕ := fun _ => .conflict
  /-- Internal reversals before and after a false-to-true boundary reversal. -/
  forward : ℕ → ℕ → List (Fin n) × List (Fin n)

/-- Read a numbered table as a typed generator-implementation certificate. -/
@[expose] def Cert.ofTable {g : Γ a b} {H : Diagram Γ' a b}
    (t : Cert.Table (a.length + H.innerCount)) : Cert g H :=
  let code β := (boundaryList a b).foldr (fun p n => Nat.bit (β p) n) 0
  let moves β (x : Fin a.length ⊕ Fin b.length) :=
    movesOfForward t.forward (code β) (Sum.elim Fin.val (fun i => a.length + i.val) x)
  { canon := fun β y =>
      ((H.boundaryPartial β).lookup y).getD ((t.innerBits (code β)).contains (H.num y))
    rounds := t.rounds
    refute := fun β => t.refute (code β)
    pre := fun β x => ((moves β x).1).map H.numEquiv.symm
    post := fun β x => ((moves β x).2).map H.numEquiv.symm }

variable (I I') in
/-- The certificates are valid. Configurations are enumerated only on the boundary. -/
structure Cert.Valid {g : Γ a b} {H : Diagram Γ' a b} (c : Cert g H) : Prop where
  /-- The canonical configuration restricts to the prescribed boundary. -/
  boundary (β) (x) : c.canon β (H.bmap x) = β x
  /-- Allowed boundary configurations have legal canonical extensions. -/
  legal_canon (β) : GenLegal I g β → (H.graph I').Legal (c.canon β)
  /-- Forbidden boundary configurations have checked refutations. -/
  refutation (β) : ¬GenLegal I g β →
    (c.refute β).check (numVertexList I' H) c.rounds (H.numOrient (H.boundaryPartial β)) = true
  /-- Allowed boundary reversals have checked paths between canonical configurations. -/
  move (β) (x) : GenLegal I g β → GenLegal I g (reverse β x) →
    MoveCert I' H (c.canon β) (c.pre β x) (H.bmap x) (c.post β x) (c.canon (reverse β x))

instance {g : Γ a b} {H : Diagram Γ' a b} (c : Cert g H) : Decidable (c.Valid I I') :=
  decidable_of_iff (_ ∧ _ ∧ _ ∧ _)
    ⟨fun ⟨hb, hl, hr, hm⟩ => ⟨hb, hl, hr, hm⟩,
      fun h => ⟨h.boundary, h.legal_canon, h.refutation, h.move⟩⟩

/-- **An open simulation of a generator, from valid certificates.** -/
@[expose] def OpenSim.ofCert {g : Γ a b} {H : Diagram Γ' a b} (c : Cert g H) (hc : c.Valid I I') :
    OpenSim I I' (gen g) H where
  ι := H.bmap
  ι_injective := (Function.surjective_comp_right_iff_injective (γ := Bool)).1 fun β =>
    ⟨c.canon β, funext (hc.boundary β)⟩
  ι_top _ := rfl
  ι_bottom _ := rfl
  enc := c.canon
  enc_ι := hc.boundary
  sound {t} ht := by
    refine (genLegal_iff g _).1 (by_contra fun h => ?_)
    exact not_extends_of_refutes ((c.refute _).refutes (hc.refutation _ h)) ht
      (extends_boundaryPartial H t)
  legal_enc hs := hc.legal_canon _ ((genLegal_iff g _).2 hs)
  lift x hs hs' := by
    obtain ⟨hpre, hflip, hpost, hend⟩ :=
      hc.move _ x ((genLegal_iff g _).2 hs) ((genLegal_iff g _).2 hs')
    exact ⟨_, hpre.innerReach, hflip, hend ▸ hpost.innerReach⟩

end Diagram

end Cslib.Complexity.NCL
