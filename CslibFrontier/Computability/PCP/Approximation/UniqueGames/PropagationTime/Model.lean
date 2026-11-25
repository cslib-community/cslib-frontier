/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.Approximation.UniqueGames.Propagation
public import CslibFrontier.Computability.WordRAM.ListOutput
import all CslibFrontier.Computability.PCP.Approximation.UniqueGames.Propagation
import Mathlib.Data.List.GetD

/-!
# Incidence-list model, flat encodings, and resource bounds for Word-RAM label propagation

This module provides the pure incidence-list construction (`insertEdge`, `buckets`), flat Word-RAM
input/output encodings (`encodeEdge`, `encode`, `encodeSolution`, `decodeSolution`), word-width and
instruction-count bounds (`wordBound`, `timeBound`), and public output register indices
(`Reg.outBase`, `Reg.ok`) for Word-RAM unique-games label propagation.

## Main definitions

* `Cslib.Complexity.UniqueGames.Propagation.insertEdge`,
  `Cslib.Complexity.UniqueGames.Propagation.buckets`: pure incidence-list construction.
* `Cslib.Complexity.UniqueGames.Propagation.encodeEdge`,
  `Cslib.Complexity.UniqueGames.Propagation.encode`: flat Word-RAM input encoding of
  `Graph (Fin L → Fin L)`.
* `Cslib.Complexity.UniqueGames.Propagation.encodeSolution`,
  `Cslib.Complexity.UniqueGames.Propagation.decodeSolution`: list-output encoding and exact decoder
  for `Option (ℕ → Fin L)`.
* `Cslib.Complexity.UniqueGames.Propagation.wordBound`,
  `Cslib.Complexity.UniqueGames.Propagation.timeBound`: word-width and `O(L · (slots g + |E|))`
  instruction bounds.
* `Cslib.Complexity.UniqueGames.Propagation.Reg.outBase`,
  `Cslib.Complexity.UniqueGames.Propagation.Reg.ok`: output-array address and decision registers.

## Main results

* `Cslib.Complexity.UniqueGames.Propagation.buckets_spec`,
  `Cslib.Complexity.UniqueGames.Propagation.buckets_getD`: `buckets` computes `adj g`.
* `Cslib.Complexity.UniqueGames.Propagation.length_encodeEdge`,
  `Cslib.Complexity.UniqueGames.Propagation.length_encode`: word lengths of `encodeEdge` and
  `encode`.
* `Cslib.Complexity.UniqueGames.Propagation.decodeSolution_encodeSolution`: `decodeSolution`
  recovers `solve (List.finRange L) g` from `encodeSolution`.
* `Cslib.Complexity.UniqueGames.Propagation.Fits.inputFits_encode`: fitting `wordBound g` suffices
  for `InputFits w (encode g)`.
-/

public section

namespace Cslib.Complexity.UniqueGames.Propagation

open Cslib.PCP Cslib.PCP.Encoded Cslib.WordRAM

/-! ## Incidence lists -/

section Buckets

variable {α : Type}

/-- Insert an edge into the incidence lists of its endpoints (once for a loop). -/
@[expose] def insertEdge (bs : List (List (Edge (α → α)))) (e : Edge (α → α)) :
    List (List (Edge (α → α))) :=
  if e.src = e.dst then bs.set e.src (e :: bs.getD e.src [])
  else (bs.set e.src (e :: bs.getD e.src [])).set e.dst (e :: bs.getD e.dst [])

/-- The incidence lists of the slots below `n`, preserving the order of the edges. -/
@[expose] def buckets (n : ℕ) (l : List (Edge (α → α))) : List (List (Edge (α → α))) :=
  l.foldr (fun e bs => insertEdge bs e) (List.replicate n [])

/-- With endpoints below `n`, `buckets n l` has `n` entries, the incidence lists in `l`. -/
theorem buckets_spec (n : ℕ) (l : List (Edge (α → α))) (hl : ∀ e ∈ l, e.src < n ∧ e.dst < n) :
    (buckets n l).length = n ∧ ∀ u, (buckets n l).getD u [] = l.filter (incident u) := by
  induction l with
  | nil =>
    refine ⟨List.length_replicate, fun u => ?_⟩
    change (List.replicate n []).getD u [] = []
    by_cases hu : u < n
    · exact List.getD_replicate _ hu
    · exact List.getD_eq_default _ _ (by simpa only [List.length_replicate, not_lt] using hu)
  | cons e l ih =>
    obtain ⟨hlen, hget⟩ := ih fun d hd => hl d (List.mem_cons_of_mem _ hd)
    have he := hl e List.mem_cons_self
    change (insertEdge (buckets n l) e).length = n ∧
      ∀ u, (insertEdge (buckets n l) e).getD u [] = (e :: l).filter (incident u)
    unfold insertEdge
    split_ifs with hsd
    · refine ⟨by rw [List.length_set, hlen], fun u => ?_⟩
      have hs : e.src < (buckets n l).length := by rw [hlen]; exact he.1
      by_cases hu : u = e.src
      · subst hu
        rw [List.getD_eq_getElem?_getD, List.getElem?_set_self hs, Option.getD_some,
          hget, List.filter_cons]
        simp only [incident, beq_self_eq_true, Bool.true_or, ↓reduceIte]
      · rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hu),
          ← List.getD_eq_getElem?_getD, hget, List.filter_cons]
        rw [ite_eq_right fun h => by
          simp only [incident, hsd, Bool.or_self, beq_iff_eq] at h
          exact hu (h.symm.trans hsd.symm)]
    · have hlen1 : ((buckets n l).set e.src (e :: (buckets n l).getD e.src [])).length = n := by
        rw [List.length_set, hlen]
      refine ⟨by rw [List.length_set, hlen1], fun u => ?_⟩
      have hs : e.src < (buckets n l).length := by rw [hlen]; exact he.1
      have hd : e.dst < ((buckets n l).set e.src (e :: (buckets n l).getD e.src [])).length := by
        rw [hlen1]; exact he.2
      by_cases hu : u = e.dst
      · subst hu
        rw [List.getD_eq_getElem?_getD, List.getElem?_set_self hd, Option.getD_some,
          hget, List.filter_cons]
        simp only [incident, beq_self_eq_true, Bool.or_true, ↓reduceIte]
      · by_cases hu' : u = e.src
        · subst hu'
          rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hu),
            List.getElem?_set_self hs, Option.getD_some, hget, List.filter_cons]
          simp only [incident, beq_self_eq_true, Bool.true_or, ↓reduceIte]
        · rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hu),
            List.getElem?_set_ne (Ne.symm hu'), ← List.getD_eq_getElem?_getD,
            hget, List.filter_cons]
          rw [ite_eq_right fun h => by
            simp only [incident, Bool.or_eq_true, beq_iff_eq] at h
            exact h.elim (fun h => hu' h.symm) (fun h => hu h.symm)]

/-- The incidence lists of a graph's slots are its `adj` lists. -/
theorem buckets_getD (g : Graph (α → α)) (u : ℕ) :
    (buckets (slots g) g.edges).getD u [] = adj g u :=
  (buckets_spec _ _ fun _ he => ⟨src_lt_slots he, dst_lt_slots he⟩).2 u

end Buckets

/-! ## Word-RAM encoding, decoding, and resource bounds -/

/-- Words encoding one directed edge over `Fin L`: `src`, `dst`, and `constraint 0, …,
constraint (L - 1)`. -/
@[expose] def encodeEdge {L : ℕ} (e : Edge (Fin L → Fin L)) : List ℕ :=
  e.src :: e.dst :: (List.finRange L).map fun a => (e.constraint a).val

/-- Each encoded edge over `Fin L` occupies `L + 2` words. -/
@[simp] theorem length_encodeEdge {L : ℕ} (e : Edge (Fin L → Fin L)) :
    (encodeEdge e).length = L + 2 := by
  simp only [encodeEdge, List.length_cons, List.length_map, List.length_finRange]

/-- Flat Word-RAM input encoding of a unique-games instance over `Fin L`:
`[L, g.vertices, |g.edges|]` followed by the `(L + 2)`-word records of `g.edges`. -/
@[expose] def encode {L : ℕ} (g : Graph (Fin L → Fin L)) : List ℕ :=
  L :: g.vertices :: g.edges.length :: g.edges.flatMap encodeEdge

/-- Total word length of `encode g`. -/
@[simp] theorem length_encode {L : ℕ} (g : Graph (Fin L → Fin L)) :
    (encode g).length = 3 + g.edges.length * (L + 2) := by
  simp only [encode, List.length_cons, List.length_flatMap, length_encodeEdge,
    List.map_const', List.sum_replicate, smul_eq_mul]
  omega

/-- Length-prefixed output words representing `Option (ℕ → Fin L)` on the `n` vertex slots:
`[0]` for `none`, and `1 :: [(σ 0).val, …, (σ (n - 1)).val]` for `some σ`. -/
@[expose] def encodeSolution {L : ℕ} (n : ℕ) : Option (ℕ → Fin L) → List ℕ
  | none => [0]
  | some σ => 1 :: (List.range n).map fun v => (σ v).val

/-- Reconstruct `Option (ℕ → Fin L)` from `encodeSolution`, defaulting slots at or above the
recorded array length to `0` (`default : Fin L`). -/
@[expose] def decodeSolution (L : ℕ) [NeZero L] : List ℕ → Option (ℕ → Fin L)
  | 1 :: vals => some fun v =>
      if h : vals.getD v 0 < L then ⟨vals.getD v 0, h⟩ else default
  | _ => none

private theorem length_run_table {α : Type} [DecidableEq α] [Inhabited α] (labels : List α)
    (g : Graph (α → α)) : (run labels g).table.length = slots g := by
  unfold run
  suffices ∀ (es : List (Edge (α → α))) (S : State α),
      S.table.length = slots g → (es.foldl (step labels g) S).table.length = slots g by
    exact this g.edges (init g) List.length_replicate
  intro es S hS
  induction es generalizing S with
  | nil => exact hS
  | cons e es ih => exact ih _ ((length_step labels g S e).trans hS)

/-- `decodeSolution L` recovers `solve (List.finRange L) g` identically on every `v : ℕ`. -/
theorem decodeSolution_encodeSolution {L : ℕ} [NeZero L] (g : Graph (Fin L → Fin L)) :
    decodeSolution L (encodeSolution (slots g) (solve (List.finRange L) g)) =
      solve (List.finRange L) g := by
  unfold solve
  split_ifs with hc
  · simp only [encodeSolution, decodeSolution, Option.some.injEq]
    funext v
    by_cases hv : v < slots g
    · have hget :=
        List.getD_map_range (fun u => (labelling (List.finRange L) g u).val) 0 hv
      simp only [hget, Fin.is_lt, ↓reduceDIte, Fin.eta]
    · have hget : ((List.range (slots g)).map fun u => (labelling (List.finRange L) g u).val).getD
          v 0 = 0 :=
        List.getD_eq_default _ _
          (by simpa only [List.length_map, List.length_range, not_lt] using hv)
      have hnone : (run (List.finRange L) g).get v = none := by
        simp only [State.get]
        exact List.getD_eq_default _ _ (by rw [length_run_table]; omega)
      simp only [hget, NeZero.pos L, ↓reduceDIte]
      simp only [labelling, hnone, Option.elim_none]
      rfl
  · rfl

/-- Word-width bound sufficient for all addresses, indices, and products during Word-RAM label
propagation on `g`. -/
@[expose] def wordBound {L : ℕ} (g : Graph (Fin L → Fin L)) : ℕ :=
  (L + 6) * (slots g + g.edges.length + 2)

/-- Instruction bound (`O(L · (slots g + |g.edges|))`) for `solveCode`, `program`, and
`decideProgram`. -/
@[expose] def timeBound {L : ℕ} (g : Graph (Fin L → Fin L)) : ℕ :=
  (16 * L + 80) * slots g + (120 * L + 300) * g.edges.length + 80

/-- Fitting `wordBound g` suffices for `InputFits w (encode g)`. -/
theorem Fits.inputFits_encode {L w : ℕ} {g : Graph (Fin L → Fin L)} (hw : Fits w (wordBound g)) :
    InputFits w (encode g) := by
  have hbound : 3 + g.edges.length * (L + 2) ≤ wordBound g := by
    simp only [wordBound]
    nlinarith
  refine ⟨hw.of_le (by rw [length_encode]; exact hbound), fun x hx => hw.of_le ?_⟩
  simp only [encode, List.mem_cons, List.mem_flatMap] at hx
  have hv_le : g.vertices ≤ slots g := vertices_le_slots g
  rcases hx with rfl | rfl | rfl | ⟨e, he, hex⟩
  · simp only [wordBound]; nlinarith
  · simp only [wordBound]; nlinarith
  · simp only [wordBound]; nlinarith
  · have hs : e.src < slots g := src_lt_slots he
    have hd : e.dst < slots g := dst_lt_slots he
    simp only [encodeEdge, List.mem_cons, List.mem_map] at hex
    rcases hex with rfl | rfl | ⟨a, _, rfl⟩
    · simp only [wordBound]; nlinarith
    · simp only [wordBound]; nlinarith
    · have ha : (e.constraint a).val < L := (e.constraint a).isLt
      simp only [wordBound]; nlinarith

namespace Reg

/-- Output register holding the base address of the length-prefixed `encodeSolution` array. -/
abbrev outBase : Fin 34 := 16

/-- Output register holding `(solve (List.finRange L) g).isSome.toNat` (`1` or `0`). -/
abbrev ok : Fin 34 := 19

end Reg

end Cslib.Complexity.UniqueGames.Propagation
