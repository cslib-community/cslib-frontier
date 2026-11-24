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
import CslibFrontier.Computability.WordRAM.CountingLoop
import CslibFrontier.Computability.WordRAM.SymbolicExec
import CslibFrontier.Foundations.Data.List.Lookup
import CslibFrontier.Foundations.Data.List.RowMajor
import Mathlib.Data.List.GetD

/-!
# Word-RAM label propagation for unique games

`Cslib.Complexity.UniqueGames.Propagation.program` and
`Cslib.Complexity.UniqueGames.Propagation.decideProgram` implement the label-propagation algorithm
`Cslib.Complexity.UniqueGames.Propagation.solve` [Khot, Section 2.4][Khot2010] as a uniform
`Basis.standard` word-RAM program over finite label sets `Fin L` (`[NeZero L]`).

Every operation of the algorithm is executed and charged in word-RAM step semantics:
* scanning the input edges to compute `N = slots g` (`O(|E|)` instructions);
* building per-slot linked incidence lists in memory representing `buckets N g.edges` (`O(|E|)`
  instructions, relying on zero-initialized cells above the input for empty list heads);
* outer iteration over edges, initializing each unvisited seed's table and candidate array (`O(L)`),
  exploring its connected component via an explicit stack in memory (`O(L)` per incident edge for
  forward composition, first-preimage inversion, backward composition, and candidate pruning), and
  freezing every slot of the component to the first surviving guess (`O(L)` per slot);
* extracting the final labelling into the output array (`O(N)`) and checking every edge (`O(|E|)`).

On an instance `g : Graph (Fin L → Fin L)` (`[NeZero L]`) with `N = slots g` vertex slots and
`E = g.edges.length` edges, at any word width `w` satisfying `Fits w (wordBound g)`, both programs
halt in at most `timeBound g` (`O(L · (N + E))`) instructions: `program` outputs
`encodeSolution (slots g) (solve (List.finRange L) g)` via `ExecutesList` (from which
`decodeSolution L` recovers `solve (List.finRange L) g` identically), and `decideProgram` outputs
`(solve (List.finRange L) g).isSome.toNat` via `Executes`.

The Word-RAM verification reuses the private state definitions, traversal invariants, and
potential/step lemmas of `UniqueGames.Propagation` (such as `State.unvisited`, `State.potential`,
`State.wpot`, `Step`, `foldl_visit_step`, and `unvisited_settle`), which this module reads through
`import all`.

## Main definitions

* `Cslib.Complexity.UniqueGames.Propagation.insertEdge`,
  `Cslib.Complexity.UniqueGames.Propagation.buckets`: pure incidence-list construction.
* `Cslib.Complexity.UniqueGames.Propagation.encodeEdge`,
  `Cslib.Complexity.UniqueGames.Propagation.encode`: flat word-RAM input encoding of
  `Graph (Fin L → Fin L)`.
* `Cslib.Complexity.UniqueGames.Propagation.encodeSolution`,
  `Cslib.Complexity.UniqueGames.Propagation.decodeSolution`: list-output encoding and exact decoder
  for `Option (ℕ → Fin L)`.
* `Cslib.Complexity.UniqueGames.Propagation.wordBound`,
  `Cslib.Complexity.UniqueGames.Propagation.timeBound`: word-width and `O(L · (slots g + |E|))`
  instruction bounds.
* `Cslib.Complexity.UniqueGames.Propagation.Reg.outBase`,
  `Cslib.Complexity.UniqueGames.Propagation.Reg.ok`: output-array address and decision registers.
* `Cslib.Complexity.UniqueGames.Propagation.solveCode`,
  `Cslib.Complexity.UniqueGames.Propagation.program`,
  `Cslib.Complexity.UniqueGames.Propagation.decideProgram`: structured and flat word-RAM programs.

## Main results

* `Cslib.Complexity.UniqueGames.Propagation.buckets_spec`,
  `Cslib.Complexity.UniqueGames.Propagation.buckets_getD`: `buckets` computes `adj g`.
* `Cslib.Complexity.UniqueGames.Propagation.decodeSolution_encodeSolution`: `decodeSolution`
  recovers `solve (List.finRange L) g` from `encodeSolution`.
* `Cslib.Complexity.UniqueGames.Propagation.Fits.inputFits_encode`: fitting `wordBound g` suffices
  for `InputFits w (encode g)`.
* `Cslib.Complexity.UniqueGames.Propagation.solveCode_spec`: structured `ExecWithin` specification
  for `solveCode` certifying both `Reg.ok` and the `outputList` at `Reg.outBase`.
* `Cslib.Complexity.UniqueGames.Propagation.program_spec`,
  `Cslib.Complexity.UniqueGames.Propagation.program_spec_of_wellFormed`,
  `Cslib.Complexity.UniqueGames.Propagation.computesListInTime_program`: `ExecutesList` and
  `Program.ComputesListInTime` certificates for full assignment recovery.
* `Cslib.Complexity.UniqueGames.Propagation.decideProgram_spec`,
  `Cslib.Complexity.UniqueGames.Propagation.computesInTime_decideProgram`: `Executes` and
  `Program.ComputesInTime` certificates for satisfiability / `solve.isSome`.

## References

* [S. Khot, *On the Unique Games Conjecture*, Section 2.4][Khot2010]
-/

public section

namespace Cslib.Complexity.UniqueGames.Propagation

open Cslib.PCP Cslib.PCP.Encoded Cslib.WordRAM Cslib.WordRAM.Block

/-! ## Incidence lists -/

section Buckets

variable {α : Type}

private theorem getD_set_ite {β : Type} (l : List β) {i : ℕ} (hi : i < l.length) (x d : β)
    (u : ℕ) : (l.set i x).getD u d = if u = i then x else l.getD u d := by
  split_ifs with h
  · subst h
    simp only [List.getD_eq_getElem?_getD, List.getElem?_set_self hi, Option.getD_some]
  · exact List.getD_set_ne (Ne.symm h)

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
      rw [getD_set_ite _ hs, List.filter_cons, hget, hget]
      by_cases hu : u = e.src
      · subst hu; simp only [incident, beq_self_eq_true, Bool.true_or, ↓reduceIte]
      · rw [ite_eq_right fun h => absurd h hu, ite_eq_right fun h => by
          simp only [incident, hsd, Bool.or_self, beq_iff_eq] at h
          exact hu (h.symm.trans hsd.symm)]
    · have hlen1 : ((buckets n l).set e.src (e :: (buckets n l).getD e.src [])).length = n := by
        rw [List.length_set, hlen]
      refine ⟨by rw [List.length_set, hlen1], fun u => ?_⟩
      have hs : e.src < (buckets n l).length := by rw [hlen]; exact he.1
      have hd : e.dst < ((buckets n l).set e.src (e :: (buckets n l).getD e.src [])).length := by
        rw [hlen1]; exact he.2
      rw [getD_set_ite _ hd, getD_set_ite _ hs, List.filter_cons, hget, hget, hget]
      by_cases hu : u = e.dst
      · subst hu; simp only [incident, beq_self_eq_true, Bool.or_true, ↓reduceIte]
      · by_cases hu' : u = e.src
        · subst hu'; simp only [incident, hsd, beq_self_eq_true, Bool.true_or, ↓reduceIte]
        · rw [ite_eq_right fun h => absurd h hu, ite_eq_right fun h => absurd h hu',
            ite_eq_right fun h => by
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

@[simp] theorem length_encodeEdge {L : ℕ} (e : Edge (Fin L → Fin L)) :
    (encodeEdge e).length = L + 2 := by
  simp only [encodeEdge, List.length_cons, List.length_map, List.length_finRange]

/-- Flat word-RAM input encoding of a unique-games instance over `Fin L`:
`[L, g.vertices, |g.edges|]` followed by the `(L + 2)`-word records of `g.edges`. -/
@[expose] def encode {L : ℕ} (g : Graph (Fin L → Fin L)) : List ℕ :=
  L :: g.vertices :: g.edges.length :: g.edges.flatMap encodeEdge

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

/-! ## Registers and structured Word-RAM program -/

namespace Reg

private abbrev rZero : Fin 34 := 0
private abbrev rOne : Fin 34 := 1
private abbrev rTwo : Fin 34 := 2
private abbrev rL : Fin 34 := 3
private abbrev rStride : Fin 34 := 4
private abbrev rN : Fin 34 := 5
private abbrev rE : Fin 34 := 6
private abbrev rEdgeBase : Fin 34 := 7
private abbrev rHeadBase : Fin 34 := 8
private abbrev rNodeBase : Fin 34 := 9
private abbrev rVisBase : Fin 34 := 10
private abbrev rTabBase : Fin 34 := 11
private abbrev rCandBase : Fin 34 := 12
private abbrev rInvBase : Fin 34 := 13
private abbrev rStackBase : Fin 34 := 14
private abbrev rCompBase : Fin 34 := 15
/-- Output register holding the base address of the length-prefixed `encodeSolution` array. -/
abbrev outBase : Fin 34 := 16
private abbrev rStackLen : Fin 34 := 17
private abbrev rCompLen : Fin 34 := 18
/-- Output register holding `(solve (List.finRange L) g).isSome.toNat` (`1` or `0`). -/
abbrev ok : Fin 34 := 19
private abbrev rOuterIdx : Fin 34 := 20
private abbrev rNodeFree : Fin 34 := 21
private abbrev rRem : Fin 34 := 22
private abbrev rChosen : Fin 34 := 23
private abbrev rCurNode : Fin 34 := 24
private abbrev rEdgeIdx : Fin 34 := 25
private abbrev rSrc : Fin 34 := 26
private abbrev rDst : Fin 34 := 27
private abbrev rLabIdx : Fin 34 := 28
private abbrev rTmp1 : Fin 34 := 29
private abbrev rTmp2 : Fin 34 := 30
private abbrev rTmp3 : Fin 34 := 31
private abbrev rTmp4 : Fin 34 := 32
private abbrev rTmp5 : Fin 34 := 33

end Reg

open Reg

private def initSetupCode : Code .standard 34 := ram[
  rZero ← #0;
  rOne ← #1;
  rTwo ← #2;
  rL ← *rOne;
  rStride ← rL + rTwo;
  rN ← *rTwo;
  rTmp1 ← #3;
  rE ← *rTmp1;
  rEdgeBase ← #4;
  rOuterIdx ← rZero ]

private def slotsBody : Code .standard 34 := ram[
  rTmp1 ← rOuterIdx * rStride;
  rTmp1 ← rEdgeBase + rTmp1;
  rSrc ← *rTmp1;
  rTmp2 ← rTmp1 + rOne;
  rDst ← *rTmp2;
  rTmp3 ← rSrc + rOne;
  if rN < rTmp3 then [ rN ← rTmp3 ] else [ rN ← rN ];
  rTmp3 ← rDst + rOne;
  if rN < rTmp3 then [ rN ← rTmp3 ] else [ rN ← rN ];
  rOuterIdx ← rOuterIdx + rOne ]

private def slotsLoop : Code .standard 34 :=
  .loop (.lt rOuterIdx rE) slotsBody

private def layoutSetupA : Code .standard 34 := ram[
  rHeadBase ← *rZero;
  rHeadBase ← rHeadBase + rOne;
  rNodeBase ← rHeadBase + rN;
  rTmp1 ← #4;
  rTmp1 ← rTmp1 * rE;
  rVisBase ← rNodeBase + rTmp1;
  rTabBase ← rVisBase + rN ]

private def layoutSetupB : Code .standard 34 := ram[
  rTmp1 ← rN * rL;
  rCandBase ← rTabBase + rTmp1;
  rInvBase ← rCandBase + rL;
  rStackBase ← rInvBase + rL;
  rCompBase ← rStackBase + rN;
  outBase ← rCompBase + rN;
  rNodeFree ← rNodeBase;
  rOuterIdx ← rZero ]

private def layoutSetupCode : Code .standard 34 := ram[
  ⟪layoutSetupA⟫;
  ⟪layoutSetupB⟫ ]

private def prependToSlot (slotReg : Fin 34) : Code .standard 34 := ram[
  rTmp3 ← rHeadBase + slotReg;
  rTmp4 ← *rTmp3;
  *rNodeFree ← rEdgeIdx;
  rTmp5 ← rNodeFree + rOne;
  *rTmp5 ← rTmp4;
  *rTmp3 ← rNodeFree;
  rNodeFree ← rNodeFree + rTwo ]

private def bucketsHead : Code .standard 34 := ram[
  rEdgeIdx ← rE - rOne;
  rEdgeIdx ← rEdgeIdx - rOuterIdx;
  rTmp1 ← rEdgeIdx * rStride;
  rTmp1 ← rEdgeBase + rTmp1;
  rSrc ← *rTmp1;
  rTmp2 ← rTmp1 + rOne;
  rDst ← *rTmp2 ]

private def bucketsBody : Code .standard 34 := ram[
  ⟪bucketsHead⟫;
  ⟪prependToSlot rSrc⟫;
  if rSrc = rDst then [ rOuterIdx ← rOuterIdx ] else [ ⟪prependToSlot rDst⟫ ];
  rOuterIdx ← rOuterIdx + rOne ]

private def bucketsLoop : Code .standard 34 :=
  .loop (.lt rOuterIdx rE) bucketsBody

private def extendFwdBody : Code .standard 34 := ram[
  rTmp4 ← rTmp2 + rLabIdx;
  rTmp4 ← *rTmp4;
  rTmp4 ← rTmp4 + rTwo;
  rTmp4 ← rEdgeIdx + rTmp4;
  rTmp4 ← *rTmp4;
  rTmp5 ← rTmp3 + rLabIdx;
  *rTmp5 ← rTmp4;
  rLabIdx ← rLabIdx + rOne ]

private def invInitBody : Code .standard 34 := ram[
  rTmp4 ← rInvBase + rLabIdx;
  *rTmp4 ← rL;
  rLabIdx ← rLabIdx + rOne ]

private def invFillBody : Code .standard 34 := ram[
  rTmp4 ← rLabIdx + rTwo;
  rTmp4 ← rEdgeIdx + rTmp4;
  rTmp4 ← *rTmp4;
  rTmp5 ← rInvBase + rTmp4;
  rTmp4 ← *rTmp5;
  if rTmp4 = rL then [ *rTmp5 ← rLabIdx ] else [ rLabIdx ← rLabIdx ];
  rLabIdx ← rLabIdx + rOne ]

private def invLoopsCode : Code .standard 34 := ram[
  rLabIdx ← rZero;
  ⟪.loop (.lt rLabIdx rL) invInitBody⟫;
  rLabIdx ← rZero;
  ⟪.loop (.lt rLabIdx rL) invFillBody⟫ ]

private def extendBwdBody : Code .standard 34 := ram[
  rTmp4 ← rTmp2 + rLabIdx;
  rTmp4 ← *rTmp4;
  rTmp5 ← rInvBase + rTmp4;
  rTmp5 ← *rTmp5;
  if rTmp5 = rL then [ rTmp5 ← rTmp4 ] else [ rTmp5 ← rTmp5 ];
  rTmp4 ← rTmp3 + rLabIdx;
  *rTmp4 ← rTmp5;
  rLabIdx ← rLabIdx + rOne ]

private def edgeVisLoad : Code .standard 34 := ram[
  rTmp1 ← rVisBase + rSrc;
  rTmp1 ← *rTmp1;
  rTmp2 ← rVisBase + rDst;
  rTmp2 ← *rTmp2 ]

private def extendPrep (fromReg toReg : Fin 34) : Code .standard 34 := ram[
  rTmp2 ← fromReg * rL;
  rTmp2 ← rTabBase + rTmp2;
  rTmp3 ← toReg * rL;
  rTmp3 ← rTabBase + rTmp3;
  rLabIdx ← rZero ]

private def extendPush (slotReg : Fin 34) : Code .standard 34 := ram[
  rTmp4 ← rVisBase + slotReg;
  *rTmp4 ← rOne;
  rTmp4 ← rStackBase + rStackLen;
  *rTmp4 ← slotReg;
  rStackLen ← rStackLen + rOne ]

private def extendCode : Code .standard 34 := ram[
  ⟪edgeVisLoad⟫;
  if rTmp1 = rOne then [
    if rTmp2 = rZero then [
      ⟪extendPrep rSrc rDst⟫;
      ⟪.loop (.lt rLabIdx rL) extendFwdBody⟫;
      ⟪extendPush rDst⟫
    ] else [ rLabIdx ← rLabIdx ]
  ] else [
    if rTmp2 = rOne then [
      ⟪invLoopsCode⟫;
      ⟪extendPrep rDst rSrc⟫;
      ⟪.loop (.lt rLabIdx rL) extendBwdBody⟫;
      ⟪extendPush rSrc⟫
    ] else [ rLabIdx ← rLabIdx ] ] ]

private def pruneBody : Code .standard 34 := ram[
  rTmp1 ← rCandBase + rLabIdx;
  rTmp4 ← *rTmp1;
  if rTmp4 = rOne then [
    rTmp4 ← rTmp2 + rLabIdx;
    rTmp4 ← *rTmp4;
    rTmp4 ← rTmp4 + rTwo;
    rTmp4 ← rEdgeIdx + rTmp4;
    rTmp4 ← *rTmp4;
    rTmp5 ← rTmp3 + rLabIdx;
    rTmp5 ← *rTmp5;
    if rTmp4 = rTmp5 then [ rLabIdx ← rLabIdx ] else [ *rTmp1 ← rZero ]
  ] else [ rLabIdx ← rLabIdx ];
  rLabIdx ← rLabIdx + rOne ]

private def pruneCode : Code .standard 34 := ram[
  ⟪edgeVisLoad⟫;
  if rTmp1 = rOne then [
    if rTmp2 = rOne then [
      ⟪extendPrep rSrc rDst⟫;
      ⟪.loop (.lt rLabIdx rL) pruneBody⟫
    ] else [ rLabIdx ← rLabIdx ]
  ] else [ rLabIdx ← rLabIdx ] ]

private def visitListHead : Code .standard 34 := ram[
  rEdgeIdx ← *rCurNode;
  rTmp1 ← rCurNode + rOne;
  rCurNode ← *rTmp1;
  rTmp1 ← rEdgeIdx * rStride;
  rEdgeIdx ← rEdgeBase + rTmp1;
  rSrc ← *rEdgeIdx;
  rTmp1 ← rEdgeIdx + rOne;
  rDst ← *rTmp1 ]

private def visitListBody : Code .standard 34 := ram[
  ⟪visitListHead⟫;
  ⟪extendCode⟫;
  ⟪pruneCode⟫ ]

private def visitListLoop : Code .standard 34 :=
  .loop (.lt rZero rCurNode) visitListBody

private def scanPop : Code .standard 34 := ram[
  rStackLen ← rStackLen - rOne;
  rTmp1 ← rStackBase + rStackLen;
  rChosen ← *rTmp1;
  rTmp1 ← rCompBase + rCompLen;
  *rTmp1 ← rChosen;
  rCompLen ← rCompLen + rOne;
  rTmp1 ← rHeadBase + rChosen;
  rCurNode ← *rTmp1 ]

private def scanCode : Code .standard 34 := ram[
  ⟪scanPop⟫;
  ⟪visitListLoop⟫ ]

private def exploreBody : Code .standard 34 := ram[
  if rStackLen = rZero then [ rRem ← rZero ] else [
    rRem ← rRem - rOne;
    ⟪scanCode⟫ ] ]

private def exploreCode : Code .standard 34 := ram[
  rRem ← rN;
  ⟪.loop (.lt rZero rRem) exploreBody⟫ ]

private def startBody : Code .standard 34 := ram[
  rTmp1 ← rTmp2 + rLabIdx;
  *rTmp1 ← rLabIdx;
  rTmp1 ← rCandBase + rLabIdx;
  *rTmp1 ← rOne;
  rLabIdx ← rLabIdx + rOne ]

private def startPre : Code .standard 34 := ram[
  rTmp2 ← rSrc * rL;
  rTmp2 ← rTabBase + rTmp2;
  rLabIdx ← rZero ]

private def startPost : Code .standard 34 := ram[
  rTmp1 ← rVisBase + rSrc;
  *rTmp1 ← rOne;
  *rStackBase ← rSrc;
  rStackLen ← rOne;
  rCompLen ← rZero ]

private def startCode : Code .standard 34 := ram[
  ⟪startPre⟫;
  ⟪.loop (.lt rLabIdx rL) startBody⟫;
  ⟪startPost⟫ ]

private def pickChosenBody : Code .standard 34 := ram[
  if rTmp3 = rZero then [
    rTmp1 ← rCandBase + rLabIdx;
    rTmp2 ← *rTmp1;
    if rTmp2 = rOne then [ rChosen ← rLabIdx; rTmp3 ← rOne ] else [ rLabIdx ← rLabIdx ]
  ] else [ rLabIdx ← rLabIdx ];
  rLabIdx ← rLabIdx + rOne ]

private def freezeSlotBody : Code .standard 34 := ram[
  rTmp4 ← rTmp2 + rLabIdx;
  *rTmp4 ← rTmp3;
  rLabIdx ← rLabIdx + rOne ]

private def freezeLoadV : Code .standard 34 := ram[
  rTmp1 ← rCompLen - rOne;
  rTmp1 ← rTmp1 - rRem;
  rTmp1 ← rCompBase + rTmp1;
  rSrc ← *rTmp1;
  rTmp1 ← rVisBase + rSrc;
  rTmp1 ← *rTmp1 ]

private def freezePrep : Code .standard 34 := ram[
  rTmp2 ← rSrc * rL;
  rTmp2 ← rTabBase + rTmp2;
  rTmp3 ← rTmp2 + rChosen;
  rTmp3 ← *rTmp3;
  rLabIdx ← rZero ]

private def freezeCompBody : Code .standard 34 := ram[
  ⟪freezeLoadV⟫;
  if rTmp1 = rOne then [
    ⟪freezePrep⟫;
    ⟪.loop (.lt rLabIdx rL) freezeSlotBody⟫
  ] else [ rRem ← rRem ];
  rRem ← rRem + rOne ]

private def settlePickInit : Code .standard 34 := ram[
  rChosen ← rZero;
  rTmp3 ← rZero;
  rLabIdx ← rZero ]

private def settleCode : Code .standard 34 := ram[
  ⟪settlePickInit⟫;
  ⟪.loop (.lt rLabIdx rL) pickChosenBody⟫;
  rRem ← rZero;
  ⟪.loop (.lt rRem rCompLen) freezeCompBody⟫;
  rCompLen ← rZero ]

private def stepHead : Code .standard 34 := ram[
  rTmp1 ← rOuterIdx * rStride;
  rTmp1 ← rEdgeBase + rTmp1;
  rSrc ← *rTmp1;
  rTmp1 ← rVisBase + rSrc;
  rTmp1 ← *rTmp1 ]

private def stepBody : Code .standard 34 := ram[
  ⟪stepHead⟫;
  if rTmp1 = rZero then [
    ⟪startCode⟫;
    ⟪exploreCode⟫;
    ⟪settleCode⟫
  ] else [ rOuterIdx ← rOuterIdx ];
  rOuterIdx ← rOuterIdx + rOne ]

private def stepsLoop : Code .standard 34 :=
  .loop (.lt rOuterIdx rE) stepBody

private def extractBody : Code .standard 34 := ram[
  rTmp1 ← rVisBase + rOuterIdx;
  rTmp1 ← *rTmp1;
  if rTmp1 = rOne then [
    rTmp2 ← rOuterIdx * rL;
    rTmp2 ← rTabBase + rTmp2;
    rTmp2 ← *rTmp2
  ] else [
    rTmp2 ← rZero ];
  rTmp3 ← outBase + rTwo;
  rTmp3 ← rTmp3 + rOuterIdx;
  *rTmp3 ← rTmp2;
  rOuterIdx ← rOuterIdx + rOne ]

private def extractCode : Code .standard 34 := ram[
  rOuterIdx ← rZero;
  ⟪.loop (.lt rOuterIdx rN) extractBody⟫ ]

private def checkBody : Code .standard 34 := ram[
  rTmp1 ← rOuterIdx * rStride;
  rEdgeIdx ← rEdgeBase + rTmp1;
  rSrc ← *rEdgeIdx;
  rTmp1 ← rEdgeIdx + rOne;
  rDst ← *rTmp1;
  rTmp2 ← outBase + rTwo;
  rTmp3 ← rTmp2 + rSrc;
  rTmp3 ← *rTmp3;
  rTmp4 ← rTmp2 + rDst;
  rTmp4 ← *rTmp4;
  rTmp5 ← rTmp3 + rTwo;
  rTmp5 ← rEdgeIdx + rTmp5;
  rTmp5 ← *rTmp5;
  if rTmp5 = rTmp4 then [ rOuterIdx ← rOuterIdx ] else [ ok ← rZero ];
  rOuterIdx ← rOuterIdx + rOne ]

private def checkInit : Code .standard 34 := ram[
  ok ← rOne;
  rOuterIdx ← rZero ]

private def checkCode : Code .standard 34 := ram[
  ⟪checkInit⟫;
  ⟪.loop (.lt rOuterIdx rE) checkBody⟫ ]

private def finishCode : Code .standard 34 := ram[
  rTmp1 ← outBase + rOne;
  if ok = rOne then [
    rTmp2 ← rN + rOne;
    *outBase ← rTmp2;
    *rTmp1 ← rOne
  ] else [
    *outBase ← rOne;
    *rTmp1 ← rZero ] ]

private def resetStateCode : Code .standard 34 := ram[
  rStackLen ← rZero;
  rCompLen ← rZero;
  rOuterIdx ← rZero ]

/-- Structured word-RAM program running label propagation on `encode g`: leaves the base address of
`encodeSolution (slots g) (solve (List.finRange L) g)` in `Reg.outBase` and
`(solve (List.finRange L) g).isSome.toNat` in `Reg.ok`. -/
def solveCode : Code .standard 34 :=
  (ram[ ⟪initSetupCode⟫; ⟪slotsLoop⟫; ⟪layoutSetupCode⟫ ]).seq
    (bucketsLoop.seq
      (resetStateCode.seq
        (stepsLoop.seq
          (extractCode.seq
            (checkCode.seq finishCode)))))

/-- Flat word-RAM program halting with the address `Reg.outBase` of the length-prefixed solution
`encodeSolution (slots g) (solve (List.finRange L) g)`. -/
def program : Program .standard 34 :=
  solveCode.program outBase

/-- Flat word-RAM program halting with `(solve (List.finRange L) g).isSome.toNat` in `Reg.ok`. -/
def decideProgram : Program .standard 34 :=
  solveCode.program ok

/-! ## Memory layout and Phase 1–2 symbolic execution (setup, `slots`, `buckets`) -/

section Verification

@[wram_arith] private abbrev headBase {L : ℕ} (g : Graph (Fin L → Fin L)) : ℕ :=
  4 + g.edges.length * (L + 2)

@[wram_arith] private abbrev nodeBase {L : ℕ} (g : Graph (Fin L → Fin L)) : ℕ :=
  headBase g + slots g

@[wram_arith] private abbrev visBase {L : ℕ} (g : Graph (Fin L → Fin L)) : ℕ :=
  nodeBase g + 4 * g.edges.length

@[wram_arith] private abbrev tabBase {L : ℕ} (g : Graph (Fin L → Fin L)) : ℕ :=
  visBase g + slots g

@[wram_arith] private abbrev candBase {L : ℕ} (g : Graph (Fin L → Fin L)) : ℕ :=
  tabBase g + slots g * L

@[wram_arith] private abbrev invBase {L : ℕ} (g : Graph (Fin L → Fin L)) : ℕ :=
  candBase g + L

@[wram_arith] private abbrev stackBase {L : ℕ} (g : Graph (Fin L → Fin L)) : ℕ :=
  invBase g + L

@[wram_arith] private abbrev compBase {L : ℕ} (g : Graph (Fin L → Fin L)) : ℕ :=
  stackBase g + slots g

@[wram_arith] private abbrev outBaseAddr {L : ℕ} (g : Graph (Fin L → Fin L)) : ℕ :=
  compBase g + slots g

private theorem outBaseAddr_lt_wordBound {L : ℕ} (g : Graph (Fin L → Fin L)) :
    outBaseAddr g + slots g + 2 ≤ wordBound g := by
  simp only [outBaseAddr, compBase, stackBase, invBase, candBase, tabBase, visBase, nodeBase,
    headBase, wordBound]
  nlinarith

private theorem fits_top {L w a : ℕ} {g : Graph (Fin L → Fin L)} (hw : Fits w (wordBound g))
    (ha : a ≤ outBaseAddr g + slots g + 2) : Fits w a :=
  hw.of_le (ha.trans (outBaseAddr_lt_wordBound g))

private theorem edge_end_le_headBase {L j : ℕ} {g : Graph (Fin L → Fin L)}
    (hj : j < g.edges.length) : 4 + j * (L + 2) + (L + 2) ≤ headBase g := by
  have : j * (L + 2) + (L + 2) ≤ g.edges.length * (L + 2) := by
    simpa only [Nat.succ_mul] using Nat.mul_le_mul_right (L + 2) hj
  simp only [headBase]
  omega

private theorem edge_end_le_wordBound {L j : ℕ} {g : Graph (Fin L → Fin L)}
    (hj : j < g.edges.length) : 4 + j * (L + 2) + (L + 2) ≤ wordBound g :=
  (edge_end_le_headBase hj).trans (by wram_omega : headBase g ≤ outBaseAddr g + slots g + 2)
    |>.trans (outBaseAddr_lt_wordBound g)

private theorem edges_lt_wordBound {L : ℕ} (g : Graph (Fin L → Fin L)) :
    g.edges.length + slots g + L + 4 ≤ wordBound g := by
  simp only [wordBound]
  nlinarith

private theorem exec_nop {w : ℕ} (r : Fin 34) (x : Data 34) :
    Exec (B := .standard) w (.op (.copy r r)) x x 1 := by
  have h : x.set r (x.regs r) = x := by cases x; simp only [Data.set, Function.update_eq_self]
  simpa only [h] using
    (Exec.copy : Exec (B := .standard) w (.op (.copy r r)) x (x.set r (x.regs r)) 1)

/-- Input memory cells `0 .. 3 + E * (L + 2)` hold the header and edge records of `g`. -/
private structure InputAt {L : ℕ} (g : Graph (Fin L → Fin L)) (mem : ℕ → ℕ) : Prop where
  mem0 : mem 0 = 3 + g.edges.length * (L + 2)
  mem1 : mem 1 = L
  mem2 : mem 2 = g.vertices
  mem3 : mem 3 = g.edges.length
  edge_src : ∀ j (hj : j < g.edges.length), mem (4 + j * (L + 2)) = g.edges[j].src
  edge_dst : ∀ j (hj : j < g.edges.length), mem (4 + j * (L + 2) + 1) = g.edges[j].dst
  edge_val : ∀ j (hj : j < g.edges.length) a (ha : a < L),
    mem (4 + j * (L + 2) + 2 + a) = (g.edges[j].constraint ⟨a, ha⟩).val

private theorem InputAt.frame {L : ℕ} {g : Graph (Fin L → Fin L)} {mem mem' : ℕ → ℕ}
    (h : InputAt g mem) (heq : ∀ a < headBase g, mem' a = mem a) : InputAt g mem' where
  mem0 := by rw [heq 0 (by simp only [headBase]; omega)]; exact h.mem0
  mem1 := by rw [heq 1 (by simp only [headBase]; omega)]; exact h.mem1
  mem2 := by rw [heq 2 (by simp only [headBase]; omega)]; exact h.mem2
  mem3 := by rw [heq 3 (by simp only [headBase]; omega)]; exact h.mem3
  edge_src j hj := by
    have := edge_end_le_headBase hj
    rw [heq _ (by omega)]; exact h.edge_src j hj
  edge_dst j hj := by
    have := edge_end_le_headBase hj
    rw [heq _ (by omega)]; exact h.edge_dst j hj
  edge_val j hj a ha := by
    have := edge_end_le_headBase hj
    rw [heq _ (by omega)]; exact h.edge_val j hj a ha

private theorem inputAt_init {L : ℕ} (g : Graph (Fin L → Fin L)) :
    InputAt g (Data.init (encode g) : Data 34).mem ∧
      ∀ a, headBase g ≤ a → (Data.init (encode g) : Data 34).mem a = 0 := by
  have hm0 : (Data.init (encode g) : Data 34).mem 0 = 3 + g.edges.length * (L + 2) := by
    rw [Data.init_mem_zero, length_encode]
  have hm1 : (Data.init (encode g) : Data 34).mem 1 = L := by
    rw [Data.init_mem_succ]; simp only [encode, List.getD_cons_zero]
  have hm2 : (Data.init (encode g) : Data 34).mem 2 = g.vertices := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, Data.init_mem_succ]
    simp only [encode, List.getD_cons_succ, List.getD_cons_zero]
  have hm3 : (Data.init (encode g) : Data 34).mem 3 = g.edges.length := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, Data.init_mem_succ]
    simp only [encode, List.getD_cons_succ, List.getD_cons_zero]
  have hedge : ∀ j (hj : j < g.edges.length) r (hr : r < L + 2),
      (Data.init (encode g) : Data 34).mem (4 + j * (L + 2) + r) =
        (encodeEdge g.edges[j])[r]'(by simp only [length_encodeEdge]; exact hr) := by
    intro j hj r hr
    rw [show 4 + j * (L + 2) + r = (3 + (j * (L + 2) + r)) + 1 by omega, Data.init_mem_succ]
    simp only [encode, List.getD_eq_getElem?_getD]
    change ([L, g.vertices, g.edges.length] ++ g.edges.flatMap encodeEdge)[
      3 + (j * (L + 2) + r)]?.getD 0 = _
    rw [List.getElem?_append_right (by simp only [List.length_cons, List.length_nil]; omega)]
    simp only [List.length_cons, List.length_nil, Nat.add_sub_cancel_left]
    rw [List.getElem?_flatMap_mul_add g.edges encodeEdge (L + 2)
      (fun _ _ => length_encodeEdge _) hj hr,
      List.getElem?_eq_getElem (by simp only [length_encodeEdge]; exact hr)]
    rfl
  refine ⟨⟨hm0, hm1, hm2, hm3, ?_, ?_, ?_⟩, ?_⟩
  · intro j hj
    simpa only [encodeEdge, List.getElem_cons_zero, Nat.add_zero] using hedge j hj 0 (by omega)
  · intro j hj
    simpa only [encodeEdge, List.getElem_cons_succ, List.getElem_cons_zero] using
      hedge j hj 1 (by omega)
  · intro j hj a ha
    have h := hedge j hj (a + 2) (by omega)
    rw [show 4 + j * (L + 2) + (a + 2) = 4 + j * (L + 2) + 2 + a by omega] at h
    simpa only [encodeEdge, List.getElem_cons_succ, List.getElem_map, List.getElem_finRange,
      Fin.cast_mk] using h
  · intro a ha
    have ha1 : a = (a - 1) + 1 := by simp only [headBase] at ha; omega
    rw [ha1, Data.init_mem_succ]
    exact List.getD_eq_default _ _ (by rw [length_encode]; simp only [headBase] at ha; omega)

/-- Fixed layout registers `0 .. 16` established after `layoutSetupCode`. -/
private structure ConstRegs {L : ℕ} (g : Graph (Fin L → Fin L)) (x : Data 34) : Prop where
  zero : x.regs rZero = 0
  one : x.regs rOne = 1
  two : x.regs rTwo = 2
  regL : x.regs rL = L
  stride : x.regs rStride = L + 2
  regN : x.regs rN = slots g
  regE : x.regs rE = g.edges.length
  edgeB : x.regs rEdgeBase = 4
  headB : x.regs rHeadBase = headBase g
  nodeB : x.regs rNodeBase = nodeBase g
  visB : x.regs rVisBase = visBase g
  tabB : x.regs rTabBase = tabBase g
  candB : x.regs rCandBase = candBase g
  invB : x.regs rInvBase = invBase g
  stackB : x.regs rStackBase = stackBase g
  compB : x.regs rCompBase = compBase g
  outB : x.regs outBase = outBaseAddr g

@[local wram_simps] private theorem ConstRegs.write_iff {L : ℕ} {g : Graph (Fin L → Fin L)}
    (x : Data 34) (a v : ℕ) : ConstRegs g (x.write a v) ↔ ConstRegs g x := by
  simp only [Data.write]
  exact ⟨fun h => ⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7, h.8, h.9, h.10, h.11, h.12, h.13, h.14,
      h.15, h.16, h.17⟩,
    fun h => ⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7, h.8, h.9, h.10, h.11, h.12, h.13, h.14,
      h.15, h.16, h.17⟩⟩

@[local wram_simps] private theorem ConstRegs.set_iff {L : ℕ} {g : Graph (Fin L → Fin L)}
    (x : Data 34) {r : Fin 34} (v : ℕ) (hr : 17 ≤ r.val) :
    ConstRegs g (x.set r v) ↔ ConstRegs g x := by
  have ne (i : Fin 34) (hi : i.val < 17) : i ≠ r := fun h => by rw [h] at hi; omega
  constructor <;> intro h <;> exact
    { zero := by simpa only [Data.set_regs_of_ne (ne rZero (by decide))] using h.zero
      one := by simpa only [Data.set_regs_of_ne (ne rOne (by decide))] using h.one
      two := by simpa only [Data.set_regs_of_ne (ne rTwo (by decide))] using h.two
      regL := by simpa only [Data.set_regs_of_ne (ne rL (by decide))] using h.regL
      stride := by simpa only [Data.set_regs_of_ne (ne rStride (by decide))] using h.stride
      regN := by simpa only [Data.set_regs_of_ne (ne rN (by decide))] using h.regN
      regE := by simpa only [Data.set_regs_of_ne (ne rE (by decide))] using h.regE
      edgeB := by simpa only [Data.set_regs_of_ne (ne rEdgeBase (by decide))] using h.edgeB
      headB := by simpa only [Data.set_regs_of_ne (ne rHeadBase (by decide))] using h.headB
      nodeB := by simpa only [Data.set_regs_of_ne (ne rNodeBase (by decide))] using h.nodeB
      visB := by simpa only [Data.set_regs_of_ne (ne rVisBase (by decide))] using h.visB
      tabB := by simpa only [Data.set_regs_of_ne (ne rTabBase (by decide))] using h.tabB
      candB := by simpa only [Data.set_regs_of_ne (ne rCandBase (by decide))] using h.candB
      invB := by simpa only [Data.set_regs_of_ne (ne rInvBase (by decide))] using h.invB
      stackB := by simpa only [Data.set_regs_of_ne (ne rStackBase (by decide))] using h.stackB
      compB := by simpa only [Data.set_regs_of_ne (ne rCompBase (by decide))] using h.compB
      outB := by simpa only [Data.set_regs_of_ne (ne outBase (by decide))] using h.outB }

private structure Phase3Regs (x y : Data 34) : Prop where
  edgeIdx : y.regs rEdgeIdx = x.regs rEdgeIdx
  src : y.regs rSrc = x.regs rSrc
  dst : y.regs rDst = x.regs rDst
  stackLen : y.regs rStackLen = x.regs rStackLen
  compLen : y.regs rCompLen = x.regs rCompLen
  curNode : y.regs rCurNode = x.regs rCurNode
  rem : y.regs rRem = x.regs rRem
  outerIdx : y.regs rOuterIdx = x.regs rOuterIdx

private theorem Phase3Regs.refl (x : Data 34) : Phase3Regs x x :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem Phase3Regs.trans {x y z : Data 34}
    (h2 : Phase3Regs y z) (h1 : Phase3Regs x y) : Phase3Regs x z :=
  ⟨h2.1.trans h1.1, h2.2.trans h1.2, h2.3.trans h1.3, h2.4.trans h1.4,
    h2.5.trans h1.5, h2.6.trans h1.6, h2.7.trans h1.7, h2.8.trans h1.8⟩

@[local wram_simps] private theorem Phase3Regs.write_iff (x y : Data 34) (a v : ℕ) :
    Phase3Regs x (y.write a v) ↔ Phase3Regs x y := by
  simp only [Data.write]
  exact ⟨fun h => ⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7, h.8⟩,
    fun h => ⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7, h.8⟩⟩

@[local wram_simps] private theorem Phase3Regs.set_iff (x y : Data 34) {r : Fin 34} (v : ℕ)
    (hr : r.val ≤ 16 ∨ 28 ≤ r.val) :
    Phase3Regs x (y.set r v) ↔ Phase3Regs x y := by
  have ne (i : Fin 34) (hi : 17 ≤ i.val ∧ i.val ≤ 27) : i ≠ r := fun h => by
    rw [h] at hi; omega
  constructor <;> intro h <;> exact
    { edgeIdx := by simpa only [Data.set_regs_of_ne (ne rEdgeIdx (by decide))] using h.edgeIdx
      src := by simpa only [Data.set_regs_of_ne (ne rSrc (by decide))] using h.src
      dst := by simpa only [Data.set_regs_of_ne (ne rDst (by decide))] using h.dst
      stackLen := by simpa only [Data.set_regs_of_ne (ne rStackLen (by decide))] using h.stackLen
      compLen := by simpa only [Data.set_regs_of_ne (ne rCompLen (by decide))] using h.compLen
      curNode := by simpa only [Data.set_regs_of_ne (ne rCurNode (by decide))] using h.curNode
      rem := by simpa only [Data.set_regs_of_ne (ne rRem (by decide))] using h.rem
      outerIdx := by simpa only [Data.set_regs_of_ne (ne rOuterIdx (by decide))] using h.outerIdx }

private def slotsPrefix {C : Type} (g : Graph C) (k : ℕ) : ℕ :=
  (g.edges.take k).foldl (fun n e => max n (max e.src e.dst + 1)) g.vertices

private theorem slotsPrefix_succ {C : Type} (g : Graph C) {k : ℕ} (hk : k < g.edges.length) :
    slotsPrefix g (k + 1) =
      max (slotsPrefix g k) (max g.edges[k].src g.edges[k].dst + 1) := by
  rw [slotsPrefix, List.take_succ_eq_append_getElem hk, List.foldl_append, List.foldl_cons,
    List.foldl_nil]
  rfl

private theorem slotsPrefix_le_slots {C : Type} (g : Graph C) (k : ℕ) :
    slotsPrefix g k ≤ slots g := by
  have hsplit : g.edges = g.edges.take k ++ g.edges.drop k := (List.take_append_drop k g.edges).symm
  unfold slots slotsPrefix
  conv_rhs => rw [hsplit, List.foldl_append]
  exact slots_mono _ _

private theorem initSetup_spec {L w : ℕ} (g : Graph (Fin L → Fin L))
    (hinp : InputAt g (Data.init (encode g) : Data 34).mem) (hw : Fits w (wordBound g)) :
    ∃ y, ExecWithin w initSetupCode (Data.init (encode g)) y 10 ∧
      y.regs rZero = 0 ∧ y.regs rOne = 1 ∧ y.regs rTwo = 2 ∧ y.regs rL = L ∧
      y.regs rStride = L + 2 ∧ y.regs rN = g.vertices ∧ y.regs rE = g.edges.length ∧
      y.regs rEdgeBase = 4 ∧ y.regs rOuterIdx = 0 ∧
      y.mem = (Data.init (encode g) : Data 34).mem := by
  have hfit_hb : Fits w (headBase g + L + 2) := fits_top hw (by wram_omega)
  have : Fits w 4 := hfit_hb.of_le (by wram_omega)
  have : Fits w 3 := hfit_hb.of_le (by wram_omega)
  have : Fits w 2 := hfit_hb.of_le (by wram_omega)
  have : Fits w 1 := hfit_hb.of_le (by wram_omega)
  have : Fits w (L + 2) := hfit_hb.of_le (by wram_omega)
  unfold initSetupCode
  wram_exec [Data.init_regs, hinp.mem1, hinp.mem2, hinp.mem3]
  wram_simp

private theorem layoutSetupA_spec {L w : ℕ} (g : Graph (Fin L → Fin L)) (x : Data 34)
    (hz0 : x.regs rZero = 0) (hz1 : x.regs rOne = 1) (hz2 : x.regs rTwo = 2)
    (hzL : x.regs rL = L) (hzSt : x.regs rStride = L + 2) (hzN : x.regs rN = slots g)
    (hzE : x.regs rE = g.edges.length) (hzEB : x.regs rEdgeBase = 4)
    (hm0 : x.mem 0 = 3 + g.edges.length * (L + 2)) (hw : Fits w (wordBound g)) :
    ∃ y, ExecWithin w layoutSetupA x y 7 ∧
      y.regs rZero = 0 ∧ y.regs rOne = 1 ∧ y.regs rTwo = 2 ∧ y.regs rL = L ∧
      y.regs rStride = L + 2 ∧ y.regs rN = slots g ∧ y.regs rE = g.edges.length ∧
      y.regs rEdgeBase = 4 ∧ y.regs rHeadBase = headBase g ∧ y.regs rNodeBase = nodeBase g ∧
      y.regs rVisBase = visBase g ∧ y.regs rTabBase = tabBase g ∧ y.mem = x.mem := by
  have : Fits w 4 := fits_top hw (by wram_omega)
  have : Fits w (3 + g.edges.length * (L + 2) + 1) := fits_top hw (by wram_omega)
  have : Fits w (3 + g.edges.length * (L + 2) + 1 + slots g) := fits_top hw (by wram_omega)
  have : Fits w (4 * g.edges.length) := fits_top hw (by wram_omega)
  have : Fits w (3 + g.edges.length * (L + 2) + 1 + slots g + 4 * g.edges.length) :=
    fits_top hw (by wram_omega)
  have : Fits w (3 + g.edges.length * (L + 2) + 1 + slots g + 4 * g.edges.length + slots g) :=
    fits_top hw (by wram_omega)
  unfold layoutSetupA
  wram_exec [hz0, hz1, hzN, hzE, hm0]
  refine ⟨by wram_simp [hz0], by wram_simp [hz1], by wram_simp [hz2], by wram_simp [hzL],
    by wram_simp [hzSt], by wram_simp [hzN], by wram_simp [hzE], by wram_simp [hzEB],
    by wram_simp; wram_omega, by wram_simp; wram_omega,
    by wram_simp; wram_omega, by wram_simp; wram_omega, by wram_simp⟩

private theorem layoutSetupB_spec {L w : ℕ} (g : Graph (Fin L → Fin L)) (x : Data 34)
    (hz0 : x.regs rZero = 0) (hz1 : x.regs rOne = 1) (hz2 : x.regs rTwo = 2)
    (hzL : x.regs rL = L) (hzSt : x.regs rStride = L + 2) (hzN : x.regs rN = slots g)
    (hzE : x.regs rE = g.edges.length) (hzEB : x.regs rEdgeBase = 4)
    (hzHB : x.regs rHeadBase = headBase g) (hzNB : x.regs rNodeBase = nodeBase g)
    (hzVB : x.regs rVisBase = visBase g) (hzTB : x.regs rTabBase = tabBase g)
    (hw : Fits w (wordBound g)) :
    ∃ y, ExecWithin w layoutSetupB x y 8 ∧
      ConstRegs g y ∧ y.regs rNodeFree = nodeBase g ∧ y.regs rOuterIdx = 0 ∧ y.mem = x.mem := by
  have : Fits w (slots g * L) := fits_top hw (by wram_omega)
  have : Fits w (tabBase g + slots g * L) := fits_top hw (by wram_omega)
  have : Fits w (tabBase g + slots g * L + L) := fits_top hw (by wram_omega)
  have : Fits w (tabBase g + slots g * L + L + L) := fits_top hw (by wram_omega)
  have : Fits w (tabBase g + slots g * L + L + L + slots g) := fits_top hw (by wram_omega)
  have : Fits w (tabBase g + slots g * L + L + L + slots g + slots g) := fits_top hw (by wram_omega)
  unfold layoutSetupB
  wram_exec [hz0, hzL, hzN, hzNB, hzTB]
  refine ⟨?_, by wram_simp, by wram_simp, by wram_simp⟩
  apply ConstRegs.mk <;>
    wram_simp [hz0, hz1, hz2, hzL, hzSt, hzN, hzE, hzEB, hzHB, hzNB, hzVB, hzTB]

private theorem slotsSetup_spec {L w : ℕ} (g : Graph (Fin L → Fin L))
    (hw : Fits w (wordBound g)) :
    ∃ y, ExecWithin w (ram[ ⟪initSetupCode⟫; ⟪slotsLoop⟫; ⟪layoutSetupCode⟫ ])
        (Data.init (encode g)) y (16 * g.edges.length + 30) ∧
      ConstRegs g y ∧ InputAt g y.mem ∧ y.regs rNodeFree = nodeBase g ∧
      y.regs rOuterIdx = 0 ∧ ∀ a, headBase g ≤ a → y.mem a = 0 := by
  have hwb := outBaseAddr_lt_wordBound g
  have hewb := edges_lt_wordBound g
  obtain ⟨hinp, hzero_above⟩ := inputAt_init g
  let Pslots (k : ℕ) (x : Data 34) : Prop :=
    x.regs rZero = 0 ∧ x.regs rOne = 1 ∧ x.regs rTwo = 2 ∧ x.regs rL = L ∧
    x.regs rStride = L + 2 ∧ x.regs rN = slotsPrefix g k ∧ x.regs rE = g.edges.length ∧
    x.regs rEdgeBase = 4 ∧ x.mem = (Data.init (encode g) : Data 34).mem
  obtain ⟨x1, hx1, hz0, hz1, hz2, hzL, hzSt, hzN0, hzE, hzEB, hzIdx0, hx1m⟩ :=
    initSetup_spec (w := w) g hinp hw
  obtain ⟨x2, hx2, ⟨hz0', hz1', hz2', hzL', hzSt', hzN', hzE', hzEB', hx2m⟩, _⟩ :=
    ExecWithin.loop_count (w := w) (index := rOuterIdx) (limit := rE) (body := slotsBody)
      (N := g.edges.length) (T := 14) Pslots
      (fun y hy => hy.2.2.2.2.2.2.1)
      (fun y hy hlt => by
        obtain ⟨h0, h1, h2, hL, hSt, hN, hE, hEB, hmem⟩ := hy
        set k := y.regs rOuterIdx
        have hk_reg : y.regs rOuterIdx = k := rfl
        have hsrc_mem : y.mem (4 + k * (L + 2)) = g.edges[k].src := by
          rw [hmem]; exact hinp.edge_src k hlt
        have hdst_mem : y.mem (4 + k * (L + 2) + 1) = g.edges[k].dst := by
          rw [hmem]; exact hinp.edge_dst k hlt
        have hs_lt : g.edges[k].src < slots g := src_lt_slots (List.getElem_mem hlt)
        have hd_lt : g.edges[k].dst < slots g := dst_lt_slots (List.getElem_mem hlt)
        have hed := edge_end_le_wordBound hlt
        have : Fits w (k * (L + 2)) := hw.of_le (by omega)
        have : Fits w (4 + k * (L + 2)) := hw.of_le (by omega)
        have : Fits w (4 + k * (L + 2) + 1) := hw.of_le (by omega)
        have : Fits w (g.edges[k].src + 1) := hw.of_le (by omega)
        have : Fits w (g.edges[k].dst + 1) := hw.of_le (by omega)
        have : Fits w (k + 1) := hw.of_le (by omega)
        unfold slotsBody
        wram_exec [h0, h1, h2, hL, hSt, hN, hE, hEB, hk_reg, hsrc_mem, hdst_mem]
        all_goals
          refine ⟨⟨by wram_simp [h0], by wram_simp [h1], by wram_simp [h2], by wram_simp [hL],
            by wram_simp [hSt], ?_, by wram_simp [hE], by wram_simp [hEB],
            by wram_simp [hmem]⟩, by wram_simp⟩
          wram_simp [hN]
          rw [slotsPrefix_succ g hlt]
          omega)
      (by rw [hzIdx0]; exact Nat.zero_le _)
      (by rw [hzIdx0]; exact ⟨hz0, hz1, hz2, hzL, hzSt, hzN0, hzE, hzEB, hx1m⟩)
  rw [hzIdx0, Nat.sub_zero] at hx2
  have hzN_eq : x2.regs rN = slots g := by rw [hzN']; simp [slotsPrefix, slots]
  have hx2_mem0 : x2.mem 0 = 3 + g.edges.length * (L + 2) := by rw [hx2m]; exact hinp.mem0
  obtain ⟨x3, hx3, ha0, ha1, ha2, haL, haSt, haN, haE, haEB, haHB, haNB, haVB, haTB, hx3m⟩ :=
    layoutSetupA_spec (w := w) g x2 hz0' hz1' hz2' hzL' hzSt' hzN_eq hzE' hzEB' hx2_mem0 hw
  obtain ⟨x4, hx4, hc4, hnf4, hidx4, hx4m⟩ :=
    layoutSetupB_spec (w := w) g x3 ha0 ha1 ha2 haL haSt haN haE haEB haHB haNB haVB haTB hw
  have hmem4 : x4.mem = (Data.init (encode g) : Data 34).mem := hx4m.trans (hx3m.trans hx2m)
  exact ⟨x4, (hx1.seq (hx2.seq (hx3.seq hx4))).mono (by omega), hc4, hmem4 ▸ hinp, hnf4, hidx4,
    fun a ha => by rw [hmem4]; exact hzero_above a ha⟩

/-- Null-terminated linked list in `[nodeBase g, top)` representing a list of edges of `g`. -/
private inductive AdjChain {L : ℕ} (g : Graph (Fin L → Fin L)) (mem : ℕ → ℕ) (top : ℕ) :
    ℕ → List (Edge (Fin L → Fin L)) → Prop where
  | nil : AdjChain g mem top 0 []
  | cons {p j : ℕ} {es : List (Edge (Fin L → Fin L))} (hj : j < g.edges.length)
      (hp_lo : nodeBase g ≤ p) (hp_hi : p + 2 ≤ top) (hp0 : mem p = j)
      (htl : AdjChain g mem top (mem (p + 1)) es) :
      AdjChain g mem top p (g.edges[j] :: es)

private theorem AdjChain.frame {L : ℕ} {g : Graph (Fin L → Fin L)} {mem mem' : ℕ → ℕ}
    {top top' p : ℕ} {es : List (Edge (Fin L → Fin L))} (h : AdjChain g mem top p es)
    (htop : top ≤ top') (heq : ∀ a, nodeBase g ≤ a → a < top → mem' a = mem a) :
    AdjChain g mem' top' p es := by
  induction h with
  | nil => exact .nil
  | @cons p j es hj hlo hhi hp0 _ ih =>
    have hm0 : mem' p = j := by rw [heq p hlo (by omega)]; exact hp0
    have hm1 : mem' (p + 1) = mem (p + 1) := heq (p + 1) (by omega) (by omega)
    exact .cons hj hlo (by omega) hm0 (hm1 ▸ ih)

private theorem prepend_adjChain {L : ℕ} {g : Graph (Fin L → Fin L)} {mem : ℕ → ℕ}
    {top u j : ℕ} {bs : List (List (Edge (Fin L → Fin L)))}
    (hlen : bs.length = slots g) (hu : u < slots g) (hj : j < g.edges.length)
    (htop_lo : nodeBase g ≤ top)
    (hbs : ∀ v < slots g, AdjChain g mem top (mem (headBase g + v)) (bs.getD v [])) :
    let mem' := Function.update (Function.update (Function.update mem top j)
      (top + 1) (mem (headBase g + u))) (headBase g + u) top
    ∀ v < slots g,
      AdjChain g mem' (top + 2) (mem' (headBase g + v))
        ((bs.set u (g.edges[j] :: bs.getD u [])).getD v []) := by
  intro mem' v hv
  have hfr : ∀ a, nodeBase g ≤ a → a < top → mem' a = mem a := by
    intro a ha1 ha2
    simp only [mem', Function.update_of_ne (by simp only [nodeBase] at ha1; omega :
        a ≠ headBase g + u),
      Function.update_of_ne (by omega : a ≠ top + 1),
      Function.update_of_ne (by omega : a ≠ top)]
  rw [getD_set_ite bs (hlen ▸ hu)]
  by_cases hvu : v = u
  · subst hvu
    simp only [↓reduceIte]
    have hhd : mem' (headBase g + v) = top := Function.update_self _ _ _
    have hp0 : mem' top = j := by
      simp only [mem', Function.update_of_ne (by simp only [nodeBase] at htop_lo; omega :
          top ≠ headBase g + v),
        Function.update_of_ne (by omega : top ≠ top + 1), Function.update_self]
    have hp1 : mem' (top + 1) = mem (headBase g + v) := by
      simp only [mem', Function.update_of_ne (by simp only [nodeBase] at htop_lo; omega :
          top + 1 ≠ headBase g + v), Function.update_self]
    rw [hhd]
    refine .cons hj htop_lo (le_refl _) hp0 ?_
    rw [hp1]
    exact (hbs v hv).frame (by omega) hfr
  · simp only [hvu, ↓reduceIte]
    have hhd : mem' (headBase g + v) = mem (headBase g + v) := by
      simp only [mem', Function.update_of_ne (by omega : headBase g + v ≠ headBase g + u),
        Function.update_of_ne (by simp only [nodeBase] at htop_lo; omega :
          headBase g + v ≠ top + 1),
        Function.update_of_ne (by simp only [nodeBase] at htop_lo; omega : headBase g + v ≠ top)]
    rw [hhd]
    exact (hbs v hv).frame (by omega) hfr

/-- Invariant that `[headBase g, visBase g)` realizes `adj g u` for every `u < slots g`. -/
private def BucketsAt {L : ℕ} (g : Graph (Fin L → Fin L)) (mem : ℕ → ℕ) : Prop :=
  ∀ u < slots g, AdjChain g mem (visBase g) (mem (headBase g + u)) (adj g u)

private theorem BucketsAt.frame {L : ℕ} {g : Graph (Fin L → Fin L)} {mem mem' : ℕ → ℕ}
    (h : BucketsAt g mem) (heq : ∀ a < visBase g, mem' a = mem a) : BucketsAt g mem' := by
  intro u hu
  have hhd : mem' (headBase g + u) = mem (headBase g + u) :=
    heq _ (by simp only [visBase, nodeBase]; omega)
  rw [hhd]
  exact (h u hu).frame le_rfl fun a _ ha => heq a ha

private theorem prependToSlot_spec {L w : ℕ} (g : Graph (Fin L → Fin L)) (slotReg : Fin 34)
    (x : Data 34) (bs : List (List (Edge (Fin L → Fin L)))) (u j : ℕ)
    (hsr : slotReg = rSrc ∨ slotReg = rDst)
    (hc : ConstRegs g x) (hinp : InputAt g x.mem)
    (hslot : x.regs slotReg = u) (hj_reg : x.regs rEdgeIdx = j)
    (hlen : bs.length = slots g) (hu : u < slots g) (hj : j < g.edges.length)
    (hlo : nodeBase g ≤ x.regs rNodeFree) (hhi : x.regs rNodeFree + 2 ≤ visBase g)
    (hbs : ∀ v < slots g,
      AdjChain g x.mem (x.regs rNodeFree) (x.mem (headBase g + v)) (bs.getD v []))
    (hzero : ∀ a, visBase g ≤ a → x.mem a = 0) (hw : Fits w (wordBound g)) :
    ∃ y, ExecWithin w (prependToSlot slotReg) x y 7 ∧
      ConstRegs g y ∧ InputAt g y.mem ∧
      y.regs rNodeFree = x.regs rNodeFree + 2 ∧
      y.regs rOuterIdx = x.regs rOuterIdx ∧
      y.regs rEdgeIdx = j ∧ y.regs rSrc = x.regs rSrc ∧ y.regs rDst = x.regs rDst ∧
      (∀ v < slots g,
        AdjChain g y.mem (y.regs rNodeFree) (y.mem (headBase g + v))
          ((bs.set u (g.edges[j] :: bs.getD u [])).getD v [])) ∧
      ∀ a, visBase g ≤ a → y.mem a = 0 := by
  have hprep := prepend_adjChain hlen hu hj hlo hbs
  have : Fits w (headBase g + u) := fits_top hw (by wram_omega)
  have : Fits w (x.regs rNodeFree + 1) := fits_top hw (by wram_omega)
  have : Fits w (x.regs rNodeFree + 2) := fits_top hw (by wram_omega)
  have hfr_inp : ∀ a < headBase g,
      Function.update (Function.update (Function.update x.mem (x.regs rNodeFree) j)
        (x.regs rNodeFree + 1) (x.mem (headBase g + u))) (headBase g + u) (x.regs rNodeFree) a =
        x.mem a := fun a ha => by
    simp only [Function.update_of_ne (by omega : a ≠ headBase g + u),
      Function.update_of_ne (by simp only [nodeBase] at hlo; omega : a ≠ x.regs rNodeFree + 1),
      Function.update_of_ne (by simp only [nodeBase] at hlo; omega : a ≠ x.regs rNodeFree)]
  have hfr_zero : ∀ a, visBase g ≤ a →
      Function.update (Function.update (Function.update x.mem (x.regs rNodeFree) j)
        (x.regs rNodeFree + 1) (x.mem (headBase g + u))) (headBase g + u) (x.regs rNodeFree) a =
        0 :=
    fun a ha => by
      simp only [Function.update_of_ne (by simp only [visBase, nodeBase] at ha; omega :
          a ≠ headBase g + u),
        Function.update_of_ne (by omega : a ≠ x.regs rNodeFree + 1),
        Function.update_of_ne (by omega : a ≠ x.regs rNodeFree)]
      exact hzero a ha
  rcases hsr with rfl | rfl <;>
  · unfold prependToSlot
    wram_exec [hc.one, hc.two, hc.headB, hslot, hj_reg]
    refine ⟨by wram_simp [hc], by wram_simp; exact hinp.frame hfr_inp,
      by wram_simp, by wram_simp, by wram_simp [hj_reg], by wram_simp, by wram_simp,
      ?_, ?_⟩
    · simp only [Data.write_mem, Data.set_mem]; wram_simp; exact hprep
    · simp only [Data.write_mem, Data.set_mem]; exact hfr_zero

private theorem bucketsLoop_spec {L w : ℕ} (g : Graph (Fin L → Fin L)) {x : Data 34}
    (hc : ConstRegs g x) (hinp : InputAt g x.mem)
    (hnf : x.regs rNodeFree = nodeBase g) (hidx : x.regs rOuterIdx = 0)
    (hzero : ∀ a, headBase g ≤ a → x.mem a = 0) (hw : Fits w (wordBound g)) :
    ∃ y, ExecWithin w bucketsLoop x y (g.edges.length * 28 + 2) ∧
      ConstRegs g y ∧ InputAt g y.mem ∧ BucketsAt g y.mem ∧
      ∀ a, visBase g ≤ a → y.mem a = 0 := by
  have hwb := outBaseAddr_lt_wordBound g
  have hewb := edges_lt_wordBound g
  let bsAt (k : ℕ) := buckets (slots g) (g.edges.drop (g.edges.length - k))
  have hbs_len : ∀ k ≤ g.edges.length, (bsAt k).length = slots g := fun k _ =>
    (buckets_spec (slots g) _ fun e he => by
      have hm := List.mem_of_mem_drop he
      exact ⟨src_lt_slots hm, dst_lt_slots hm⟩).1
  let P (k : ℕ) (y : Data 34) : Prop :=
    ConstRegs g y ∧ InputAt g y.mem ∧
    nodeBase g ≤ y.regs rNodeFree ∧ y.regs rNodeFree ≤ nodeBase g + 4 * k ∧
    (∀ u < slots g,
      AdjChain g y.mem (y.regs rNodeFree) (y.mem (headBase g + u)) ((bsAt k).getD u [])) ∧
    ∀ a, visBase g ≤ a → y.mem a = 0
  have hp0 : P 0 x := by
    refine ⟨hc, hinp, by omega, by omega, fun u hu => ?_, fun a ha =>
      hzero a (by simp only [visBase, nodeBase] at ha; omega)⟩
    have hnil : (bsAt 0).getD u [] = [] := by
      change (buckets (slots g) (g.edges.drop (g.edges.length - 0))).getD u [] = []
      rw [Nat.sub_zero, List.drop_length]
      exact List.getD_replicate _ hu
    rw [hnil, hzero (headBase g + u) (Nat.le_add_right _ _)]
    exact .nil
  obtain ⟨y, hy, ⟨hyC, hyInp, hyLo, hyHi, hyAdj, hyZero⟩, _⟩ :=
    ExecWithin.loop_count (w := w) (index := rOuterIdx) (limit := rE) (body := bucketsBody)
      (N := g.edges.length) (T := 26) P
      (fun y hy => hy.1.regE)
      (fun y hy hlt => by
        obtain ⟨hyC, hyInp, hyLo, hyHi, hyAdj, hyZero⟩ := hy
        set k := y.regs rOuterIdx
        have hk_reg : y.regs rOuterIdx = k := rfl
        set j := g.edges.length - 1 - k
        have hj : j < g.edges.length := by omega
        have hdrop : g.edges.drop (g.edges.length - (k + 1)) =
            g.edges[j] :: g.edges.drop (g.edges.length - k) := by
          rw [show g.edges.length - (k + 1) = j by omega,
            show g.edges.length - k = j + 1 by omega]
          exact List.drop_eq_getElem_cons hj
        have hbs_next : bsAt (k + 1) = insertEdge (bsAt k) g.edges[j] := by
          simp only [bsAt, hdrop, buckets, List.foldr_cons]
        have hs_lt : g.edges[j].src < slots g := src_lt_slots (List.getElem_mem hj)
        have hd_lt : g.edges[j].dst < slots g := dst_lt_slots (List.getElem_mem hj)
        have hsrc_mem := hyInp.edge_src j hj
        have hdst_mem := hyInp.edge_dst j hj
        have hlen_k : (bsAt k).length = slots g := hbs_len k (by omega)
        have hed := edge_end_le_wordBound hj
        have hed_k := edge_end_le_wordBound hlt
        have : Fits w (j * (L + 2)) := hw.of_le (by omega)
        have : Fits w (4 + j * (L + 2)) := hw.of_le (by omega)
        have : Fits w (4 + j * (L + 2) + 1) := hw.of_le (by omega)
        have : Fits w (k + 1) := hw.of_le (by omega)
        have hsub : g.edges.length - 1 - k = j := rfl
        have hhead_exec : ∃ y1, ExecWithin w bucketsHead y y1 7 ∧
            ConstRegs g y1 ∧ y1.regs rEdgeIdx = j ∧ y1.regs rSrc = g.edges[j].src ∧
            y1.regs rDst = g.edges[j].dst ∧ y1.regs rNodeFree = y.regs rNodeFree ∧
            y1.regs rOuterIdx = k ∧ y1.mem = y.mem := by
          unfold bucketsHead
          wram_exec [hyC.one, hyC.stride, hyC.regE, hyC.edgeB, hk_reg, hsub, hsrc_mem, hdst_mem]
          exact ⟨by wram_simp [hyC], by wram_simp, by wram_simp, by wram_simp, by wram_simp,
            by wram_simp [hk_reg], by wram_simp⟩
        obtain ⟨y1, hy1, hy1C, hy1J, hy1Src, hy1Dst, hy1NF, hy1Idx, hy1m⟩ := hhead_exec
        obtain ⟨z1, hz1, hz1C, hz1Inp, hz1NF, hz1Idx, hz1J, hz1Src, hz1Dst, hz1Adj, hz1Zero⟩ :=
          prependToSlot_spec (w := w) g rSrc y1 (bsAt k) g.edges[j].src j (Or.inl rfl)
            hy1C (hy1m ▸ hyInp) hy1Src hy1J hlen_k hs_lt hj
            (by omega) (by simp only [visBase]; omega)
            (by rw [hy1NF, hy1m]; exact hyAdj) (by rw [hy1m]; exact hyZero) hw
        by_cases hsd : g.edges[j].src = g.edges[j].dst
        · have htail : ∃ z2, ExecWithin w
              (ram[ if rSrc = rDst then [ rOuterIdx ← rOuterIdx ] else [ ⟪prependToSlot rDst⟫ ];
                    rOuterIdx ← rOuterIdx + rOne ] : Code .standard 34) z1 z2 4 ∧
              ConstRegs g z2 ∧ z2.regs rNodeFree = z1.regs rNodeFree ∧
              z2.regs rOuterIdx = k + 1 ∧ z2.mem = z1.mem := by
            wram_exec [hz1Src, hy1Src, hz1Dst, hy1Dst, hsd, hz1Idx, hy1Idx, hz1C.one]
            exact ⟨by wram_simp [hz1C], by wram_simp, by wram_simp, by wram_simp⟩
          obtain ⟨z2, hz2, hz2C, hz2NF, hz2Idx, hz2m⟩ := htail
          refine ⟨z2, ?_, ⟨hz2C, hz2m ▸ hz1Inp,
            by rw [hz2NF, hz1NF, hy1NF]; omega,
            by rw [hz2NF, hz1NF, hy1NF]; omega,
            fun u hu => ?_, by rw [hz2m]; exact hz1Zero⟩, hz2Idx⟩
          · exact (hy1.seq (hz1.seq hz2)).mono (by omega)
          · rw [hbs_next, hz2NF, hz2m]
            simp only [insertEdge, hsd, ↓reduceIte]
            simpa only [hsd] using hz1Adj u hu
        · have hlen_k1 : ((bsAt k).set g.edges[j].src
              (g.edges[j] :: (bsAt k).getD g.edges[j].src [])).length = slots g := by
            rw [List.length_set, hlen_k]
          obtain ⟨z2, hz2, hz2C, hz2Inp, hz2NF, hz2Idx, _, _, _, hz2Adj, hz2Zero⟩ :=
            prependToSlot_spec (w := w) g rDst z1
              ((bsAt k).set g.edges[j].src (g.edges[j] :: (bsAt k).getD g.edges[j].src []))
              g.edges[j].dst j (Or.inr rfl)
              hz1C hz1Inp (hz1Dst.trans hy1Dst) hz1J hlen_k1 hd_lt hj
              (by rw [hz1NF, hy1NF]; omega)
              (by rw [hz1NF, hy1NF]; simp only [visBase]; omega) hz1Adj hz1Zero hw
          have hbr : ExecWithin w
              (ram[ if rSrc = rDst then [ rOuterIdx ← rOuterIdx ] else [ ⟪prependToSlot rDst⟫ ] ] :
                Code .standard 34)
              z1 z2 9 := by
            have hcond : ¬ (Cond.eq rSrc rDst).Holds z1 := by
              simp only [Cond.holds_eq, hz1Src, hy1Src, hz1Dst, hy1Dst, hsd, not_false_eq_true]
            exact ExecWithin.branch_neg hcond hz2
          have hinc : ∃ z3, ExecWithin w
              (ram[ rOuterIdx ← rOuterIdx + rOne ] : Code .standard 34) z2 z3 1 ∧
              ConstRegs g z3 ∧ z3.regs rNodeFree = z2.regs rNodeFree ∧
              z3.regs rOuterIdx = k + 1 ∧ z3.mem = z2.mem := by
            wram_exec [hz2Idx, hz1Idx, hy1Idx, hz2C.one]
            exact ⟨by wram_simp [hz2C], by wram_simp, by wram_simp, by wram_simp⟩
          obtain ⟨z3, hz3, hz3C, hz3NF, hz3Idx, hz3m⟩ := hinc
          refine ⟨z3, ?_, ⟨hz3C, hz3m ▸ hz2Inp,
            by rw [hz3NF, hz2NF, hz1NF, hy1NF]; omega,
            by rw [hz3NF, hz2NF, hz1NF, hy1NF]; omega,
            fun u hu => ?_, by rw [hz3m]; exact hz2Zero⟩, hz3Idx⟩
          · exact (hy1.seq (hz1.seq (hbr.seq hz3))).mono (by omega)
          · have hdst_get :
                ((bsAt k).set g.edges[j].src
                  (g.edges[j] :: (bsAt k).getD g.edges[j].src [])).getD g.edges[j].dst [] =
                (bsAt k).getD g.edges[j].dst [] := by
              rw [getD_set_ite _ (hlen_k ▸ hs_lt)]
              simp only [Ne.symm hsd, ↓reduceIte]
            simp only [hbs_next, insertEdge, hsd, ↓reduceIte, hz3NF, hz3m, ← hdst_get]
            exact hz2Adj u hu)
      (by rw [hidx]; exact Nat.zero_le _)
      (by rwa [hidx])
  rw [hidx, Nat.sub_zero] at hy
  refine ⟨y, hy, hyC, hyInp, fun u hu => ?_, hyZero⟩
  have hbsE : (bsAt g.edges.length).getD u [] = adj g u := by
    change (buckets (slots g) (g.edges.drop (g.edges.length - g.edges.length))).getD u [] = adj g u
    rw [Nat.sub_self, List.drop_zero, buckets_getD]
  rw [← hbsE]
  exact (hyAdj u hu).frame (by simp only [visBase]; omega) fun _ _ _ => rfl

/-! ## Phase 3: Component propagation (`start`, `extend`, `prune`, `scan`, `explore`, `settle`,
`stepsLoop`) -/

private theorem not_in_tabRow {L u w a : ℕ} {g : Graph (Fin L → Fin L)}
    (huw : u ≠ w) (ha : a < L) :
    ¬ (tabBase g + w * L ≤ tabBase g + u * L + a ∧
        tabBase g + u * L + a < tabBase g + w * L + L) := by
  rcases Nat.lt_or_gt_of_ne huw with h | h
  · have : u * L + L ≤ w * L := by simpa [Nat.succ_mul] using Nat.mul_le_mul_right L h
    omega
  · have : w * L + L ≤ u * L := by simpa [Nat.succ_mul] using Nat.mul_le_mul_right L h
    omega

private theorem tabRow_hi_le_candBase {L w : ℕ} {g : Graph (Fin L → Fin L)} (hw : w < slots g) :
    tabBase g + w * L + L ≤ candBase g := by
  have : w * L + L ≤ slots g * L := by simpa [Nat.succ_mul] using Nat.mul_le_mul_right L hw
  simp only [candBase]
  omega

/-- Memory and constant-register invariant between connected components. -/
private structure TableStateAt {L : ℕ} (g : Graph (Fin L → Fin L)) (S : State (Fin L))
    (x : Data 34) : Prop where
  consts : ConstRegs g x
  inp : InputAt g x.mem
  bkt : BucketsAt g x.mem
  len_table : S.table.length = slots g
  vis_none : ∀ v < slots g, S.get v = none → x.mem (visBase g + v) = 0
  vis_some : ∀ v < slots g, ∀ f, S.get v = some f →
    x.mem (visBase g + v) = 1 ∧
      ∀ a (ha : a < L), x.mem (tabBase g + v * L + a) = (f ⟨a, ha⟩).val

/-- Full search-state invariant inside one connected component's exploration. -/
private structure StateAt {L : ℕ} (g : Graph (Fin L → Fin L)) (S : State (Fin L))
    (x : Data 34) : Prop extends TableStateAt g S x where
  pot_le : S.potential ≤ slots g
  cand_mem : ∀ a (ha : a < L), x.mem (candBase g + a) = (S.cand ⟨a, ha⟩).toNat
  stack_len : x.regs rStackLen = S.stack.length
  stack_lt : ∀ u ∈ S.stack, u < slots g
  stack_mem : HoldsList (stackBase g) S.stack.reverse x.mem
  comp_len : x.regs rCompLen = S.comp.length
  comp_le : S.comp.length ≤ slots g
  comp_lt : ∀ u ∈ S.comp, u < slots g
  comp_mem : HoldsList (compBase g) S.comp.reverse x.mem

private theorem TableStateAt.frame {L : ℕ} {g : Graph (Fin L → Fin L)} {S S' : State (Fin L)}
    {x y : Data 34} (h : TableStateAt g S x) (hc : ConstRegs g y) (htab : S'.table = S.table)
    (bound : ℕ) (hb : tabBase g + slots g * L ≤ bound) (hfr : ∀ a < bound, y.mem a = x.mem a) :
    TableStateAt g S' y := by
  refine ⟨hc, h.inp.frame (fun a ha => hfr a (by wram_omega)),
    h.bkt.frame (fun a ha => hfr a (by wram_omega)), htab ▸ h.len_table,
    fun v hv hvn => by
      change S'.table.getD v none = none at hvn
      rw [htab] at hvn
      rw [hfr _ (by wram_omega)]; exact h.vis_none v hv hvn,
    fun v hv fn hvf => ?_⟩
  change S'.table.getD v none = some fn at hvf
  rw [htab] at hvf
  obtain ⟨hv1, hvtab⟩ := h.vis_some v hv fn hvf
  have hv_cb := tabRow_hi_le_candBase (g := g) hv
  exact ⟨by rw [hfr _ (by wram_omega)]; exact hv1,
    fun a ha => by rw [hfr _ (by wram_omega)]; exact hvtab a ha⟩

private theorem TableStateAt.of_eq {L : ℕ} {g : Graph (Fin L → Fin L)} {S : State (Fin L)}
    {x y : Data 34} (h : TableStateAt g S x) (hc : ConstRegs g y) (hm : y.mem = x.mem) :
    TableStateAt g S y :=
  h.frame hc rfl (tabBase g + slots g * L) le_rfl fun _ _ => congrFun hm _

private theorem StateAt.of_eq {L : ℕ} {g : Graph (Fin L → Fin L)} {S : State (Fin L)}
    {x y : Data 34} (h : StateAt g S x) (hc : ConstRegs g y)
    (hsl : y.regs rStackLen = S.stack.length) (hcl : y.regs rCompLen = S.comp.length)
    (hm : y.mem = x.mem) : StateAt g S y :=
  ⟨h.toTableStateAt.of_eq hc hm, h.pot_le, fun a ha => hm ▸ h.cand_mem a ha,
    hsl, h.stack_lt, hm ▸ h.stack_mem, hcl, h.comp_le, h.comp_lt, hm ▸ h.comp_mem⟩

private theorem StateAt.frame_inv {L : ℕ} {g : Graph (Fin L → Fin L)} {S : State (Fin L)}
    {x y : Data 34} (hS : StateAt g S x) (hc : ConstRegs g y)
    (hsl : y.regs rStackLen = S.stack.length) (hcl : y.regs rCompLen = S.comp.length)
    (hfr : ∀ a, ¬ (invBase g ≤ a ∧ a < invBase g + L) → y.mem a = x.mem a) :
    StateAt g S y :=
  ⟨hS.toTableStateAt.frame hc rfl (invBase g) (by wram_omega) (fun a ha => hfr a (by omega)),
    hS.pot_le,
    fun a ha => by rw [hfr _ (by wram_omega)]; exact hS.cand_mem a ha,
    hsl, hS.stack_lt,
    hS.stack_mem.frame (fun a _ _ => hfr _ (by wram_omega)),
    hcl, hS.comp_le, hS.comp_lt,
    hS.comp_mem.frame (fun a _ _ => hfr _ (by wram_omega))⟩

private theorem StateAt.push_slot {L : ℕ} {g : Graph (Fin L → Fin L)} {S : State (Fin L)}
    {x y : Data 34} {u : ℕ} {f : Fin L → Fin L}
    (hS : StateAt g S x) (hc : ConstRegs g y) (hu : u < slots g) (hnone : S.get u = none)
    (hrow : ∀ a (ha : a < L), y.mem (tabBase g + u * L + a) = (f ⟨a, ha⟩).val)
    (hvis : y.mem (visBase g + u) = 1)
    (hstk_mem : HoldsList (stackBase g) (S.stack.reverse ++ [u]) y.mem)
    (hstk_len : y.regs rStackLen = S.stack.length + 1)
    (hcmp_len : y.regs rCompLen = S.comp.length)
    (hframe : ∀ a,
      ¬ (tabBase g + u * L ≤ a ∧ a < tabBase g + u * L + L) →
      a ≠ visBase g + u → a ≠ stackBase g + S.stack.length → y.mem a = x.mem a) :
    StateAt g (push S u f) y := by
  have hcb := tabRow_hi_le_candBase (g := g) hu
  have hstk_le : S.stack.length < slots g := by
    have hmem : u ∈ S.unvisited := mem_unvisited (hS.len_table ▸ hu) hnone
    have hpos : 0 < S.unvisited.card := Finset.card_pos.mpr ⟨u, hmem⟩
    have hpot := hS.pot_le
    unfold State.potential at hpot
    omega
  have hfr_low : ∀ a < visBase g, y.mem a = x.mem a := fun a ha =>
    hframe a (by simp only [tabBase] at *; omega) (by omega)
      (by simp only [stackBase, invBase, candBase, tabBase] at *; omega)
  refine ⟨⟨hc, hS.inp.frame (fun a ha => hfr_low a (by simp only [visBase, nodeBase]; omega)),
      hS.bkt.frame hfr_low, length_push S u f ▸ hS.len_table, fun v hv hvn => ?_,
      fun v hv fn hvf => ?_⟩,
    (step_push (hS.len_table ▸ hu) hnone f).potential_le.trans hS.pot_le,
    fun a ha => ?_, ?_, fun v hv => ?_, ?_, hcmp_len, hS.comp_le, hS.comp_lt, ?_⟩
  · have hne : u ≠ v := by
      rintro rfl
      rw [get_push_self (hS.len_table ▸ hu)] at hvn
      nomatch hvn
    rw [get_push_ne S hne] at hvn
    rw [hframe _ (by simp only [tabBase]; omega) (by omega)
      (by simp only [stackBase, invBase, candBase, tabBase] at *; omega)]
    exact hS.vis_none v hv hvn
  · by_cases huv : u = v
    · subst huv
      rw [get_push_self (hS.len_table ▸ hu)] at hvf
      cases hvf
      exact ⟨hvis, hrow⟩
    · rw [get_push_ne S huv] at hvf
      obtain ⟨hv1, hvtab⟩ := hS.vis_some v hv fn hvf
      refine ⟨?_, fun a ha => ?_⟩
      · rw [hframe _ (by simp only [tabBase]; omega) (by omega)
          (by simp only [stackBase, invBase, candBase, tabBase] at *; omega)]
        exact hv1
      · rw [hframe _ (not_in_tabRow (Ne.symm huv) ha) (by simp only [tabBase]; omega)
          (by have := tabRow_hi_le_candBase (g := g) hv
              simp only [stackBase, invBase] at *; omega)]
        exact hvtab a ha
  · rw [show (push S u f).cand = S.cand from rfl,
      hframe _ (by omega) (by simp only [candBase, tabBase] at *; omega)
        (by simp only [stackBase, invBase] at *; omega)]
    exact hS.cand_mem a ha
  · simpa [push] using hstk_len
  · rcases List.mem_cons.mp hv with rfl | hv
    · exact hu
    · exact hS.stack_lt v hv
  · simpa [push] using hstk_mem
  · exact hS.comp_mem.frame fun a ha1 ha2 => by
      have hcl := hS.comp_le
      rw [List.length_reverse] at ha2
      exact hframe a (by simp only [compBase, stackBase, invBase] at *; omega)
        (by simp only [compBase, stackBase, invBase, candBase, tabBase] at *; omega)
        (by simp only [compBase] at *; omega)

private theorem startCode_spec {L w : ℕ} (g : Graph (Fin L → Fin L)) (S : State (Fin L))
    (x : Data 34) (s : ℕ) (hT : TableStateAt g S x) (hs_reg : x.regs rSrc = s)
    (hs : s < slots g) (hnone : S.get s = none) (hw : Fits w (wordBound g)) :
    ∃ y, ExecWithin w startCode x y (7 * L + 12) ∧
      StateAt g (start S s) y ∧ y.regs rOuterIdx = x.regs rOuterIdx := by
  have hcb := tabRow_hi_le_candBase (g := g) hs
  have : Fits w (s * L) := fits_top hw (by wram_omega)
  have hpre : ∃ x1, ExecWithin w startPre x x1 3 ∧
      ConstRegs g x1 ∧ x1.regs rSrc = s ∧ x1.regs rTmp2 = tabBase g + s * L ∧
      x1.regs rLabIdx = 0 ∧ x1.regs rOuterIdx = x.regs rOuterIdx ∧ x1.mem = x.mem := by
    have : Fits w (tabBase g + s * L) := fits_top hw (by wram_omega)
    unfold startPre
    wram_exec [hT.consts.zero, hT.consts.regL, hT.consts.tabB, hs_reg]
    exact ⟨by wram_simp [hT.consts], by wram_simp [hs_reg], by wram_simp, by wram_simp,
      by wram_simp, by wram_simp⟩
  obtain ⟨x1, hx1, hc1, hs1, htmp1, hlab1, hidx1, hm1⟩ := hpre
  let P (k : ℕ) (z : Data 34) : Prop :=
    ConstRegs g z ∧ z.regs rSrc = s ∧ z.regs rTmp2 = tabBase g + s * L ∧
    z.regs rOuterIdx = x.regs rOuterIdx ∧
    (∀ a < k, z.mem (tabBase g + s * L + a) = a) ∧
    (∀ a < k, z.mem (candBase g + a) = 1) ∧
    ∀ addr, ¬ (tabBase g + s * L ≤ addr ∧ addr < tabBase g + s * L + k) →
      ¬ (candBase g ≤ addr ∧ addr < candBase g + k) → z.mem addr = x.mem addr
  obtain ⟨x2, hx2, ⟨hc2, hs2, _, hidx2, htab2, hcand2, hfr2⟩, _⟩ :=
    ExecWithin.loop_count (w := w) (index := rLabIdx) (limit := rL) (body := startBody)
      (N := L) (T := 5) P
      (fun z hz => hz.1.regL)
      (fun z hz hk => by
        obtain ⟨hzC, hzS, hzT2, hzIdx, hzTab, hzCand, hzFr⟩ := hz
        set k := z.regs rLabIdx
        have hk_reg : z.regs rLabIdx = k := rfl
        have : Fits w (tabBase g + s * L + k) := fits_top hw (by wram_omega)
        have : Fits w (candBase g + k) := fits_top hw (by wram_omega)
        have : Fits w (k + 1) := fits_top hw (by wram_omega)
        unfold startBody
        wram_exec [hzC.one, hzC.candB, hzT2, hk_reg]
        refine ⟨⟨by wram_simp [hzC], by wram_simp [hzS], by wram_simp [hzT2],
          by wram_simp [hzIdx], ?_, ?_, ?_⟩, by wram_simp⟩
        · simp only [Data.write_mem, Data.set_mem]
          intro a ha
          rw [Function.update_of_ne (by omega : tabBase g + s * L + a ≠ candBase g + k)]
          by_cases hak : a = k
          · subst hak; exact Function.update_self _ _ _
          · rw [Function.update_of_ne (by omega : tabBase g + s * L + a ≠ tabBase g + s * L + k)]
            exact hzTab a (by omega)
        · simp only [Data.write_mem, Data.set_mem]
          intro a ha
          by_cases hak : a = k
          · subst hak; exact Function.update_self _ _ _
          · rw [Function.update_of_ne (by omega : candBase g + a ≠ candBase g + k),
              Function.update_of_ne (by omega : candBase g + a ≠ tabBase g + s * L + k)]
            exact hzCand a (by omega)
        · simp only [Data.write_mem, Data.set_mem]
          intro addr h1 h2
          rw [Function.update_of_ne (by omega : addr ≠ candBase g + k),
            Function.update_of_ne (by omega : addr ≠ tabBase g + s * L + k)]
          exact hzFr addr (by omega) (by omega))
      (by rw [hlab1]; exact Nat.zero_le _)
      (by rw [hlab1]; exact ⟨hc1, hs1, htmp1, hidx1, fun _ h => by omega, fun _ h => by omega,
        fun addr _ _ => congrFun hm1 addr⟩)
  rw [hlab1, Nat.sub_zero] at hx2
  have hpost : ∃ y, ExecWithin w startPost x2 y 5 ∧
      ConstRegs g y ∧ y.regs rStackLen = 1 ∧ y.regs rCompLen = 0 ∧
      y.regs rOuterIdx = x.regs rOuterIdx ∧
      y.mem = Function.update (Function.update x2.mem (visBase g + s) 1) (stackBase g) s := by
    have : Fits w (visBase g + s) := fits_top hw (by wram_omega)
    unfold startPost
    wram_exec [hc2.zero, hc2.one, hc2.visB, hc2.stackB, hs2]
    exact ⟨by wram_simp [hc2], by wram_simp, by wram_simp, by wram_simp [hidx2], by wram_simp⟩
  obtain ⟨y, hx3, hc3, hstk3, hcmp3, hidx3, hym⟩ := hpost
  have hfr_low : ∀ a < visBase g, y.mem a = x.mem a := fun a ha => by
    rw [hym, Function.update_of_ne (by wram_omega), Function.update_of_ne (by omega)]
    exact hfr2 a (by wram_omega) (by wram_omega)
  refine ⟨y, (hx1.seq (hx2.seq hx3)).mono (by omega), ?_, hidx3⟩
  refine ⟨⟨hc3, hT.inp.frame (fun a ha => hfr_low a (by wram_omega)),
      hT.bkt.frame hfr_low, by simp only [start, List.length_set, hT.len_table], fun v hv hvn => ?_,
      fun v hv fn hvf => ?_⟩,
    potential_start hT.len_table (hT.len_table ▸ hs),
    fun a ha => ?_, hstk3, fun u hu => ?_, ?_, hcmp3, Nat.zero_le _,
    fun _ h => by simp only [start, List.not_mem_nil] at h, holdsList_nil _ _⟩
  · have hvs : v ≠ s := by
      rintro rfl
      have hself : (start S v).get v = some id := List.getD_set_self (hT.len_table ▸ hs)
      rw [hself] at hvn; nomatch hvn
    have hvn' : S.get v = none := by
      change (S.table.set s (some id)).getD v none = none at hvn
      rwa [List.getD_set_ne (Ne.symm hvs)] at hvn
    rw [hym, Function.update_of_ne (by wram_omega), Function.update_of_ne (by omega),
      hfr2 _ (by wram_omega) (by wram_omega)]
    exact hT.vis_none v hv hvn'
  · by_cases hvs : v = s
    · subst hvs
      have hself : (start S v).get v = some id := List.getD_set_self (hT.len_table ▸ hs)
      rw [hself] at hvf; cases hvf
      exact ⟨by rw [hym, Function.update_of_ne (by wram_omega), Function.update_self],
        fun a ha => by
          rw [hym, Function.update_of_ne (by wram_omega), Function.update_of_ne (by wram_omega)]
          exact htab2 a ha⟩
    · have hvf' : S.get v = some fn := by
        change (S.table.set s (some id)).getD v none = some fn at hvf
        rwa [List.getD_set_ne (Ne.symm hvs)] at hvf
      obtain ⟨hv1, hvtab⟩ := hT.vis_some v hv fn hvf'
      have hv_cb := tabRow_hi_le_candBase (g := g) hv
      exact ⟨by
          rw [hym, Function.update_of_ne (by wram_omega), Function.update_of_ne (by omega),
            hfr2 _ (by wram_omega) (by wram_omega)]
          exact hv1,
        fun a ha => by
          rw [hym, Function.update_of_ne (by wram_omega), Function.update_of_ne (by wram_omega),
            hfr2 _ (not_in_tabRow hvs ha) (by omega)]
          exact hvtab a ha⟩
  · rw [hym, Function.update_of_ne (by wram_omega), Function.update_of_ne (by wram_omega)]
    exact hcand2 a ha
  · simp only [start, List.mem_singleton] at hu; exact hu ▸ hs
  · simp only [start, List.reverse_singleton]
    refine holdsList_cons_iff.mpr ⟨?_, holdsList_nil _ _⟩
    rw [hym]; exact Function.update_self _ _ _

private theorem extendFwdLoop_spec {L w : ℕ} (g : Graph (Fin L → Fin L)) (x : Data 34)
    (j : ℕ) (hj : j < g.edges.length) (f : Fin L → Fin L)
    (hc : ConstRegs g x) (hinp : InputAt g x.mem)
    (heptr : x.regs rEdgeIdx = 4 + j * (L + 2))
    (hsrc_lt : g.edges[j].src < slots g) (hdst_lt : g.edges[j].dst < slots g)
    (hsd : g.edges[j].src ≠ g.edges[j].dst)
    (ht2 : x.regs rTmp2 = tabBase g + g.edges[j].src * L)
    (ht3 : x.regs rTmp3 = tabBase g + g.edges[j].dst * L)
    (hlab : x.regs rLabIdx = 0)
    (hf_mem : ∀ a (ha : a < L), x.mem (tabBase g + g.edges[j].src * L + a) = (f ⟨a, ha⟩).val)
    (hw : Fits w (wordBound g)) :
    ∃ y, ExecWithin w (.loop (.lt rLabIdx rL) extendFwdBody) x y (L * 10 + 2) ∧
      ConstRegs g y ∧ Phase3Regs x y ∧
      (∀ a (ha : a < L), y.mem (tabBase g + g.edges[j].dst * L + a) =
        (g.edges[j].constraint (f ⟨a, ha⟩)).val) ∧
      ∀ addr, ¬ (tabBase g + g.edges[j].dst * L ≤ addr ∧
          addr < tabBase g + g.edges[j].dst * L + L) → y.mem addr = x.mem addr := by
  have hed := edge_end_le_headBase hj
  have hcb_src := tabRow_hi_le_candBase (g := g) hsrc_lt
  have hcb_dst := tabRow_hi_le_candBase (g := g) hdst_lt
  let eVal (a : ℕ) : ℕ :=
    if ha : a < L then (g.edges[j].constraint (f ⟨a, ha⟩)).val else 0
  let P (k : ℕ) (z : Data 34) : Prop :=
    ConstRegs g z ∧ z.regs rTmp2 = tabBase g + g.edges[j].src * L ∧
    z.regs rTmp3 = tabBase g + g.edges[j].dst * L ∧ Phase3Regs x z ∧
    (∀ i < k, z.mem (tabBase g + g.edges[j].dst * L + i) = eVal i) ∧
    ∀ addr, ¬ (tabBase g + g.edges[j].dst * L ≤ addr ∧
        addr < tabBase g + g.edges[j].dst * L + k) → z.mem addr = x.mem addr
  obtain ⟨y, hy, ⟨hyC, _, _, hyR, hyRow, hyFr⟩, _⟩ :=
    ExecWithin.loop_count (w := w) (index := rLabIdx) (limit := rL) (body := extendFwdBody)
      (N := L) (T := 8) P
      (fun z hz => hz.1.regL)
      (fun z hz hk => by
        obtain ⟨hzC, hzT2, hzT3, hzR, hzRow, hzFr⟩ := hz
        set k := z.regs rLabIdx
        have hk_reg : z.regs rLabIdx = k := rfl
        have hfk_lt := (f ⟨k, hk⟩).isLt
        have hfa : z.mem (tabBase g + g.edges[j].src * L + k) = (f ⟨k, hk⟩).val := by
          rw [hzFr _ (fun ⟨h1, h2⟩ => not_in_tabRow (g := g) hsd hk ⟨h1, by omega⟩)]
          exact hf_mem k hk
        have hcfa : z.mem (4 + j * (L + 2) + ((f ⟨k, hk⟩).val + 2)) =
            (g.edges[j].constraint (f ⟨k, hk⟩)).val := by
          rw [hzFr _ (by wram_omega),
            show 4 + j * (L + 2) + ((f ⟨k, hk⟩).val + 2) =
              4 + j * (L + 2) + 2 + (f ⟨k, hk⟩).val by omega]
          exact hinp.edge_val j hj (f ⟨k, hk⟩).val hfk_lt
        have : Fits w (tabBase g + g.edges[j].src * L + k) := fits_top hw (by wram_omega)
        have : Fits w ((f ⟨k, hk⟩).val + 2) := fits_top hw (by wram_omega)
        have : Fits w (4 + j * (L + 2) + ((f ⟨k, hk⟩).val + 2)) := fits_top hw (by wram_omega)
        have : Fits w (tabBase g + g.edges[j].dst * L + k) := fits_top hw (by wram_omega)
        have : Fits w (k + 1) := fits_top hw (by wram_omega)
        have hzE : z.regs rEdgeIdx = 4 + j * (L + 2) := hzR.edgeIdx.trans heptr
        have heVal_k : (g.edges[j].constraint (f ⟨k, hk⟩)).val = eVal k := by
          simp only [eVal, hk, ↓reduceDIte]
        have hpws := prefix_write_step hzRow hzFr
          (rfl : Function.update z.mem (tabBase g + g.edges[j].dst * L + k) (eVal k) = _)
        unfold extendFwdBody
        wram_exec [hzC.one, hzC.two, hzT2, hzT3, hzE, hk_reg, hfa, hcfa]
        refine ⟨⟨by wram_simp [hzC], by wram_simp [hzT2], by wram_simp [hzT3],
          by wram_simp [hzR], ?_, ?_⟩, by wram_simp⟩
        · simp only [Data.write_mem, Data.set_mem, heVal_k]; exact hpws.1
        · simp only [Data.write_mem, Data.set_mem, heVal_k]; exact hpws.2)
      (by rw [hlab]; exact Nat.zero_le _)
      (by rw [hlab]; exact ⟨hc, ht2, ht3, Phase3Regs.refl x, fun _ h => by omega, fun _ _ => rfl⟩)
  rw [hlab, Nat.sub_zero] at hy
  exact ⟨y, hy, hyC, hyR,
    fun a ha => by simpa only [eVal, ha, ↓reduceDIte] using hyRow a ha, hyFr⟩

private theorem invLoops_spec {L w : ℕ} (g : Graph (Fin L → Fin L)) (x : Data 34)
    (j : ℕ) (hj : j < g.edges.length)
    (hc : ConstRegs g x) (hinp : InputAt g x.mem)
    (heptr : x.regs rEdgeIdx = 4 + j * (L + 2))
    (hw : Fits w (wordBound g)) :
    ∃ y, ExecWithin w invLoopsCode x y (16 * L + 6) ∧
      ConstRegs g y ∧ Phase3Regs x y ∧
      (∀ b (hb : b < L),
        (if y.mem (invBase g + b) = L then b else y.mem (invBase g + b)) =
          (preimage (List.finRange L) g.edges[j].constraint ⟨b, hb⟩).val) ∧
      ∀ addr, ¬ (invBase g ≤ addr ∧ addr < invBase g + L) → y.mem addr = x.mem addr := by
  have hed := edge_end_le_headBase hj
  have resetLab (y0 : Data 34) (hyC : ConstRegs g y0) (hR : Phase3Regs x y0) :
      ∃ y1, ExecWithin w (ram[ rLabIdx ← rZero ] : Code .standard 34) y0 y1 1 ∧
        ConstRegs g y1 ∧ y1.regs rLabIdx = 0 ∧ Phase3Regs x y1 ∧ y1.mem = y0.mem := by
    wram_exec [hyC.zero]
    exact ⟨by wram_simp [hyC], by wram_simp, by wram_simp [hR], by wram_simp⟩
  obtain ⟨x1, hx1, hc1, hlab1, hr1, hm1⟩ := resetLab x hc (Phase3Regs.refl x)
  let Pinit (k : ℕ) (z : Data 34) : Prop :=
    ConstRegs g z ∧ Phase3Regs x z ∧
    (∀ b < k, z.mem (invBase g + b) = L) ∧
    ∀ addr, ¬ (invBase g ≤ addr ∧ addr < invBase g + k) → z.mem addr = x.mem addr
  obtain ⟨x2, hx2, ⟨hc2, hr2, hinit_inv, hfr2⟩, _⟩ :=
    ExecWithin.loop_count (w := w) (index := rLabIdx) (limit := rL) (body := invInitBody)
      (N := L) (T := 3) Pinit
      (fun z hz => hz.1.regL)
      (fun z hz hk => by
        obtain ⟨hzC, hzR, hzInv, hzFr⟩ := hz
        set k := z.regs rLabIdx
        have hk_reg : z.regs rLabIdx = k := rfl
        have : Fits w (invBase g + k) := fits_top hw (by wram_omega)
        have : Fits w (k + 1) := fits_top hw (by wram_omega)
        have hpws := prefix_write_step (e := fun _ => L) hzInv hzFr
          (rfl : Function.update z.mem (invBase g + k) L = _)
        unfold invInitBody
        wram_exec [hzC.one, hzC.regL, hzC.invB, hk_reg]
        refine ⟨⟨by wram_simp [hzC], by wram_simp [hzR], ?_, ?_⟩, by wram_simp⟩
        · simp only [Data.write_mem, Data.set_mem]; exact hpws.1
        · simp only [Data.write_mem, Data.set_mem]; exact hpws.2)
      (by rw [hlab1]; exact Nat.zero_le _)
      (by rw [hlab1]; exact ⟨hc1, hr1, fun _ h => by omega, fun addr _ => congrFun hm1 addr⟩)
  rw [hlab1, Nat.sub_zero] at hx2
  obtain ⟨x3, hx3, hc3, hlab3, hr3, hm3⟩ := resetLab x2 hc2 hr2
  let invAt (k : ℕ) (b : ℕ) (hb : b < L) : ℕ :=
    (((List.finRange L).take k).find? fun a => decide (g.edges[j].constraint a = ⟨b, hb⟩)).elim
      L Fin.val
  let Pfill (k : ℕ) (z : Data 34) : Prop :=
    ConstRegs g z ∧ Phase3Regs x z ∧
    (∀ b (hb : b < L), z.mem (invBase g + b) = invAt k b hb) ∧
    ∀ addr, ¬ (invBase g ≤ addr ∧ addr < invBase g + L) → z.mem addr = x.mem addr
  obtain ⟨y, hx4, ⟨hyC, hyR, hyInv, hyFr⟩, _⟩ :=
    ExecWithin.loop_count (w := w) (index := rLabIdx) (limit := rL) (body := invFillBody)
      (N := L) (T := 9) Pfill
      (fun z hz => hz.1.regL)
      (fun z hz hk => by
        obtain ⟨hzC, hzR, hzInv, hzFr⟩ := hz
        set k := z.regs rLabIdx
        have hk_reg : z.regs rLabIdx = k := rfl
        set bk := (g.edges[j].constraint ⟨k, hk⟩).val
        have hbk : bk < L := (g.edges[j].constraint ⟨k, hk⟩).isLt
        have hc_mem : z.mem (4 + j * (L + 2) + (k + 2)) = bk := by
          rw [hzFr _ (by wram_omega),
            show 4 + j * (L + 2) + (k + 2) = 4 + j * (L + 2) + 2 + k by omega]
          exact hinp.edge_val j hj k hk
        have hcur_mem : z.mem (invBase g + bk) = invAt k bk hbk := hzInv bk hbk
        have htake_succ : (List.finRange L).take (k + 1) =
            (List.finRange L).take k ++ [⟨k, hk⟩] := by
          rw [List.take_succ_eq_append_getElem (by simp only [List.length_finRange]; exact hk),
            List.getElem_finRange]
          rfl
        have : Fits w (k + 2) := fits_top hw (by wram_omega)
        have : Fits w (4 + j * (L + 2) + (k + 2)) := fits_top hw (by wram_omega)
        have : Fits w (invBase g + bk) := fits_top hw (by wram_omega)
        have : Fits w (k + 1) := fits_top hw (by wram_omega)
        have hzE : z.regs rEdgeIdx = 4 + j * (L + 2) := hzR.edgeIdx.trans heptr
        cases hfind : ((List.finRange L).take k).find?
            (fun a => decide (g.edges[j].constraint a = ⟨bk, hbk⟩)) with
        | none =>
          have hcur_eq : invAt k bk hbk = L := by
            simp only [invAt, hfind, Option.elim_none]
          unfold invFillBody
          wram_exec [hzC.one, hzC.two, hzC.regL, hzC.invB, hzE, hk_reg, hc_mem, hcur_mem, hcur_eq]
          refine ⟨⟨by wram_simp [hzC], by wram_simp [hzR], ?_, ?_⟩, by wram_simp⟩
          · simp only [Data.write_mem, Data.set_mem]
            intro b hb
            by_cases hbb : b = bk
            · subst hbb; rw [Function.update_self]
              have hfin_eq : g.edges[j].constraint ⟨k, hk⟩ = ⟨bk, hb⟩ := Fin.ext rfl
              simp only [invAt, htake_succ, List.find?_append, hfind, Option.none_or,
                List.find?_cons, hfin_eq, decide_true, Option.elim_some]
            · rw [Function.update_of_ne (by omega : invBase g + b ≠ invBase g + bk), hzInv b hb]
              have hne_fin : g.edges[j].constraint ⟨k, hk⟩ ≠ ⟨b, hb⟩ :=
                fun heq => hbb (congrArg Fin.val heq).symm
              simp only [invAt, htake_succ, List.find?_append, List.find?_cons, hne_fin,
                decide_false, List.find?_nil, Option.or_none]
          · simp only [Data.write_mem, Data.set_mem]
            intro addr haddr
            rw [Function.update_of_ne (by omega : addr ≠ invBase g + bk)]
            exact hzFr addr haddr
        | some a0 =>
          have hcur_ne : invAt k bk hbk ≠ L := by
            simp only [invAt, hfind, Option.elim_some]
            exact ne_of_lt a0.isLt
          unfold invFillBody
          wram_exec [hzC.one, hzC.two, hzC.regL, hzC.invB, hzE, hk_reg, hc_mem, hcur_mem, hcur_ne]
          refine ⟨⟨by wram_simp [hzC], by wram_simp [hzR], ?_, ?_⟩, by wram_simp⟩
          · simp only [Data.set_mem]
            intro b hb
            rw [hzInv b hb]
            by_cases hbb : b = bk
            · subst hbb
              simp only [invAt, htake_succ, List.find?_append, hfind, Option.some_or]
            · have hne_fin : g.edges[j].constraint ⟨k, hk⟩ ≠ ⟨b, hb⟩ :=
                fun heq => hbb (congrArg Fin.val heq).symm
              simp only [invAt, htake_succ, List.find?_append, List.find?_cons, hne_fin,
                decide_false, List.find?_nil, Option.or_none]
          · simp only [Data.set_mem]; exact hzFr)
      (by rw [hlab3]; exact Nat.zero_le _)
      (by rw [hlab3]; refine ⟨hc3, hr3, fun b hb => ?_, fun addr haddr => ?_⟩
          · rw [hm3, hinit_inv b hb]
            simp only [invAt, List.take_zero, List.find?_nil, Option.elim_none]
          · rw [hm3]; exact hfr2 addr haddr)
  rw [hlab3, Nat.sub_zero] at hx4
  refine ⟨y, (hx1.seq (hx2.seq (hx3.seq hx4))).mono (by omega), hyC, hyR, fun b hb => ?_, hyFr⟩
  rw [hyInv b hb]
  have htakeL : (List.finRange L).take L = List.finRange L :=
    List.take_of_length_le (by simp only [List.length_finRange, le_rfl])
  simp only [invAt, htakeL, preimage]
  cases h : (List.finRange L).find? (fun a => decide (g.edges[j].constraint a = ⟨b, hb⟩)) with
  | none => simp only [↓reduceIte, Option.elim_none, Option.getD_none]
  | some a0 => simp only [Option.elim_some, ne_of_lt a0.isLt, ↓reduceIte, Option.getD_some]

private theorem extendBwdLoop_spec {L w : ℕ} (g : Graph (Fin L → Fin L)) (x : Data 34)
    (j : ℕ) (hj : j < g.edges.length) (h : Fin L → Fin L)
    (hc : ConstRegs g x)
    (hsrc_lt : g.edges[j].src < slots g) (hdst_lt : g.edges[j].dst < slots g)
    (hsd : g.edges[j].src ≠ g.edges[j].dst)
    (ht2 : x.regs rTmp2 = tabBase g + g.edges[j].dst * L)
    (ht3 : x.regs rTmp3 = tabBase g + g.edges[j].src * L)
    (hlab : x.regs rLabIdx = 0)
    (hh_mem : ∀ a (ha : a < L), x.mem (tabBase g + g.edges[j].dst * L + a) = (h ⟨a, ha⟩).val)
    (hinv_mem : ∀ b (hb : b < L),
      (if x.mem (invBase g + b) = L then b else x.mem (invBase g + b)) =
        (preimage (List.finRange L) g.edges[j].constraint ⟨b, hb⟩).val)
    (hw : Fits w (wordBound g)) :
    ∃ y, ExecWithin w (.loop (.lt rLabIdx rL) extendBwdBody) x y (L * 12 + 2) ∧
      ConstRegs g y ∧ Phase3Regs x y ∧
      (∀ a (ha : a < L), y.mem (tabBase g + g.edges[j].src * L + a) =
        (preimage (List.finRange L) g.edges[j].constraint (h ⟨a, ha⟩)).val) ∧
      ∀ addr, ¬ (tabBase g + g.edges[j].src * L ≤ addr ∧
          addr < tabBase g + g.edges[j].src * L + L) → y.mem addr = x.mem addr := by
  have hcb_src := tabRow_hi_le_candBase (g := g) hsrc_lt
  have hcb_dst := tabRow_hi_le_candBase (g := g) hdst_lt
  let eVal (a : ℕ) : ℕ :=
    if ha : a < L then (preimage (List.finRange L) g.edges[j].constraint (h ⟨a, ha⟩)).val else 0
  let P (k : ℕ) (z : Data 34) : Prop :=
    ConstRegs g z ∧ z.regs rTmp2 = tabBase g + g.edges[j].dst * L ∧
    z.regs rTmp3 = tabBase g + g.edges[j].src * L ∧ Phase3Regs x z ∧
    (∀ i < k, z.mem (tabBase g + g.edges[j].src * L + i) = eVal i) ∧
    ∀ addr, ¬ (tabBase g + g.edges[j].src * L ≤ addr ∧
        addr < tabBase g + g.edges[j].src * L + k) → z.mem addr = x.mem addr
  obtain ⟨y, hy, ⟨hyC, _, _, hyR, hyRow, hyFr⟩, _⟩ :=
    ExecWithin.loop_count (w := w) (index := rLabIdx) (limit := rL) (body := extendBwdBody)
      (N := L) (T := 10) P
      (fun z hz => hz.1.regL)
      (fun z hz hk => by
        obtain ⟨hzC, hzT2, hzT3, hzR, hzRow, hzFr⟩ := hz
        set k := z.regs rLabIdx
        have hk_reg : z.regs rLabIdx = k := rfl
        have hha : z.mem (tabBase g + g.edges[j].dst * L + k) = (h ⟨k, hk⟩).val := by
          rw [hzFr _ (fun ⟨h1, h2⟩ => not_in_tabRow (g := g) (Ne.symm hsd) hk ⟨h1, by omega⟩)]
          exact hh_mem k hk
        have hiv_fr : z.mem (invBase g + (h ⟨k, hk⟩).val) = x.mem (invBase g + (h ⟨k, hk⟩).val) :=
          hzFr _ (by wram_omega)
        have hiv_val := hinv_mem (h ⟨k, hk⟩).val (h ⟨k, hk⟩).isLt
        simp only [Fin.eta] at hiv_val
        have : Fits w (tabBase g + g.edges[j].dst * L + k) := fits_top hw (by wram_omega)
        have : Fits w (invBase g + (h ⟨k, hk⟩).val) :=
          fits_top hw (by have := (h ⟨k, hk⟩).isLt; wram_omega)
        have : Fits w (tabBase g + g.edges[j].src * L + k) := fits_top hw (by wram_omega)
        have : Fits w (k + 1) := fits_top hw (by wram_omega)
        have hpws := prefix_write_step hzRow hzFr
          (rfl : Function.update z.mem (tabBase g + g.edges[j].src * L + k) (eVal k) = _)
        have hb : (if x.mem (invBase g + (h ⟨k, hk⟩).val) = L then (h ⟨k, hk⟩).val
            else x.mem (invBase g + (h ⟨k, hk⟩).val)) = eVal k := by
          simp only [eVal, hk, ↓reduceDIte, hiv_val]
        by_cases hivL : x.mem (invBase g + (h ⟨k, hk⟩).val) = L <;>
        · unfold extendBwdBody
          wram_exec [hzC.one, hzC.regL, hzC.invB, hzT2, hzT3, hk_reg, hha, hiv_fr, hivL]
          refine ⟨⟨by wram_simp [hzC], by wram_simp [hzT2], by wram_simp [hzT3],
            by wram_simp [hzR], ?_, ?_⟩, by wram_simp⟩ <;>
          · simp only [Data.write_mem, Data.set_mem]
            simp only [hivL, ↓reduceIte] at hb
            first | (rw [hb]; exact hpws.1) | (rw [hb]; exact hpws.2))
      (by rw [hlab]; exact Nat.zero_le _)
      (by rw [hlab]; exact ⟨hc, ht2, ht3, Phase3Regs.refl x, fun _ h => by omega, fun _ _ => rfl⟩)
  rw [hlab, Nat.sub_zero] at hy
  exact ⟨y, hy, hyC, hyR,
    fun a ha => by simpa only [eVal, ha, ↓reduceDIte] using hyRow a ha, hyFr⟩

private theorem edgeVisLoad_spec {L w : ℕ} (g : Graph (Fin L → Fin L)) (S : State (Fin L))
    (x : Data 34) (j : ℕ) (hj : j < g.edges.length)
    (hS : StateAt g S x)
    (hsrc_reg : x.regs rSrc = g.edges[j].src)
    (hdst_reg : x.regs rDst = g.edges[j].dst)
    (hw : Fits w (wordBound g)) :
    ∃ x1, ExecWithin w edgeVisLoad x x1 4 ∧ ConstRegs g x1 ∧
      x1.regs rTmp1 = x.mem (visBase g + g.edges[j].src) ∧
      x1.regs rTmp2 = x.mem (visBase g + g.edges[j].dst) ∧
      Phase3Regs x x1 ∧ x1.mem = x.mem := by
  have hs_lt : g.edges[j].src < slots g := src_lt_slots (List.getElem_mem hj)
  have hd_lt : g.edges[j].dst < slots g := dst_lt_slots (List.getElem_mem hj)
  have : Fits w (visBase g + g.edges[j].src) := fits_top hw (by wram_omega)
  have : Fits w (visBase g + g.edges[j].dst) := fits_top hw (by wram_omega)
  unfold edgeVisLoad
  wram_exec [hS.consts.visB, hsrc_reg, hdst_reg]
  exact ⟨by wram_simp [hS.consts], by wram_simp, by wram_simp,
    by wram_simp [Phase3Regs.refl], by wram_simp⟩

private theorem extendPrep_spec {L w : ℕ} (g : Graph (Fin L → Fin L)) (fromReg toReg : Fin 34)
    (x1 : Data 34) (u v : ℕ)
    (hregs : (fromReg = rSrc ∧ toReg = rDst) ∨ (fromReg = rDst ∧ toReg = rSrc))
    (hc1 : ConstRegs g x1) (hu : u < slots g) (hv : v < slots g)
    (hfrom : x1.regs fromReg = u) (hto : x1.regs toReg = v)
    (hw : Fits w (wordBound g)) :
    ∃ x2, ExecWithin w (extendPrep fromReg toReg) x1 x2 5 ∧ ConstRegs g x2 ∧
      x2.regs rTmp2 = tabBase g + u * L ∧ x2.regs rTmp3 = tabBase g + v * L ∧
      x2.regs rLabIdx = 0 ∧ Phase3Regs x1 x2 ∧ x2.mem = x1.mem := by
  have hcb_u := tabRow_hi_le_candBase (g := g) hu
  have hcb_v := tabRow_hi_le_candBase (g := g) hv
  have : Fits w (u * L) := fits_top hw (by wram_omega)
  have : Fits w (v * L) := fits_top hw (by wram_omega)
  have : Fits w (tabBase g + u * L) := fits_top hw (by wram_omega)
  have : Fits w (tabBase g + v * L) := fits_top hw (by wram_omega)
  rcases hregs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  · unfold extendPrep
    wram_exec [hc1.zero, hc1.regL, hc1.tabB, hfrom, hto]
    exact ⟨by wram_simp [hc1], by wram_simp, by wram_simp, by wram_simp,
      by wram_simp [Phase3Regs.refl], by wram_simp⟩

private theorem extendPush_spec {L w : ℕ} (g : Graph (Fin L → Fin L)) (slotReg : Fin 34)
    (x : Data 34) (u stkLen : ℕ)
    (hsr : slotReg = rSrc ∨ slotReg = rDst)
    (hc : ConstRegs g x) (hu : u < slots g) (hstk_lt : stkLen < slots g)
    (hslot : x.regs slotReg = u) (hsl : x.regs rStackLen = stkLen)
    (hw : Fits w (wordBound g)) :
    ∃ y, ExecWithin w (extendPush slotReg) x y 5 ∧ ConstRegs g y ∧
      y.regs rEdgeIdx = x.regs rEdgeIdx ∧ y.regs rSrc = x.regs rSrc ∧ y.regs rDst = x.regs rDst ∧
      y.regs rStackLen = stkLen + 1 ∧ y.regs rCompLen = x.regs rCompLen ∧
      y.regs rCurNode = x.regs rCurNode ∧ y.regs rRem = x.regs rRem ∧
      y.regs rOuterIdx = x.regs rOuterIdx ∧
      y.mem = Function.update (Function.update x.mem (visBase g + u) 1)
        (stackBase g + stkLen) u := by
  have : Fits w (visBase g + u) := fits_top hw (by wram_omega)
  have : Fits w (stackBase g + stkLen) := fits_top hw (by wram_omega)
  have : Fits w (stkLen + 1) := fits_top hw (by wram_omega)
  rcases hsr with rfl | rfl <;>
  · unfold extendPush
    wram_exec [hc.one, hc.visB, hc.stackB, hslot, hsl]
    exact ⟨by wram_simp [hc], by wram_simp, by wram_simp, by wram_simp, by wram_simp,
      by wram_simp, by wram_simp, by wram_simp, by wram_simp, by wram_simp⟩

private theorem extendCode_spec {L w : ℕ} (g : Graph (Fin L → Fin L)) (S : State (Fin L))
    (x : Data 34) (j : ℕ) (hj : j < g.edges.length)
    (hS : StateAt g S x)
    (heptr : x.regs rEdgeIdx = 4 + j * (L + 2))
    (hsrc_reg : x.regs rSrc = g.edges[j].src)
    (hdst_reg : x.regs rDst = g.edges[j].dst)
    (hw : Fits w (wordBound g)) :
    ∃ y, ExecWithin w extendCode x y (28 * L + 30) ∧
      StateAt g (extend (List.finRange L) S g.edges[j]) y ∧
      y.regs rEdgeIdx = 4 + j * (L + 2) ∧
      y.regs rSrc = g.edges[j].src ∧ y.regs rDst = g.edges[j].dst ∧
      y.regs rCurNode = x.regs rCurNode ∧ y.regs rRem = x.regs rRem ∧
      y.regs rOuterIdx = x.regs rOuterIdx ∧
      ∀ a < visBase g, y.mem a = x.mem a := by
  set e := g.edges[j] with he_def
  have hs_lt : e.src < slots g := src_lt_slots (List.getElem_mem hj)
  have hd_lt : e.dst < slots g := dst_lt_slots (List.getElem_mem hj)
  obtain ⟨x1, hx1, hc1, ht1_1, ht2_1, hr1, hm1⟩ :=
    edgeVisLoad_spec (w := w) g S x j hj hS hsrc_reg hdst_reg hw
  have hnop : ExecWithin w (.op (.copy rLabIdx rLabIdx)) x1 x1 1 :=
    ⟨1, le_rfl, exec_nop rLabIdx x1⟩
  have he1 : x1.regs rEdgeIdx = 4 + j * (L + 2) := hr1.edgeIdx.trans heptr
  have hs1 : x1.regs rSrc = e.src := hr1.src.trans hsrc_reg
  have hd1 : x1.regs rDst = e.dst := hr1.dst.trans hdst_reg
  have hS1 : StateAt g S x1 :=
    hS.of_eq hc1 (hr1.stackLen.trans hS.stack_len) (hr1.compLen.trans hS.comp_len) hm1
  have hstk_of {v : ℕ} (hv : v < slots g) (hgv : S.get v = none) : S.stack.length < slots g := by
    have hmem := mem_unvisited (hS.len_table ▸ hv) hgv
    have hpos : 0 < S.unvisited.card := Finset.card_pos.mpr ⟨v, hmem⟩
    have hpot := hS.pot_le; unfold State.potential at hpot; omega
  have retSame (hext : extend (List.finRange L) S e = S)
      (hex : ExecWithin w extendCode x x1 (28 * L + 30)) :
      ∃ y, ExecWithin w extendCode x y (28 * L + 30) ∧
        StateAt g (extend (List.finRange L) S e) y ∧
        y.regs rEdgeIdx = 4 + j * (L + 2) ∧
        y.regs rSrc = e.src ∧ y.regs rDst = e.dst ∧
        y.regs rCurNode = x.regs rCurNode ∧ y.regs rRem = x.regs rRem ∧
        y.regs rOuterIdx = x.regs rOuterIdx ∧
        ∀ a < visBase g, y.mem a = x.mem a :=
    ⟨x1, hex, hext.symm ▸ hS1, he1, hs1, hd1, hr1.curNode, hr1.rem, hr1.outerIdx,
      fun a _ => by rw [hm1]⟩
  cases hgs : S.get e.src with
  | some f =>
    obtain ⟨hvis_s, htab_s⟩ := hS.vis_some e.src hs_lt f hgs
    have hc_outer : (Cond.eq rTmp1 rOne).Holds x1 := by
      simp only [Cond.holds_eq, ht1_1, ← he_def, hvis_s, hc1.one]
    cases hgd : S.get e.dst with
    | none =>
      have hvis_d : x.mem (visBase g + e.dst) = 0 := hS.vis_none e.dst hd_lt hgd
      have hsd : e.src ≠ e.dst := by intro h0; rw [← h0, hgs] at hgd; nomatch hgd
      have hc_inner : (Cond.eq rTmp2 rZero).Holds x1 := by
        simp only [Cond.holds_eq, ht2_1, ← he_def, hvis_d, hc1.zero]
      have hstk_lt : S.stack.length < slots g := hstk_of hd_lt hgd
      obtain ⟨x2, hx2, hc2, ht2_2, ht3_2, hlab2, hr2', hm2'⟩ :=
        extendPrep_spec (w := w) g rSrc rDst x1 e.src e.dst (Or.inl ⟨rfl, rfl⟩)
          hc1 hs_lt hd_lt hs1 hd1 hw
      have hr2 := hr2'.trans hr1
      have hm2 := hm2'.trans hm1
      obtain ⟨x3, hx3, hc3, hr3', hrow3, hfr3⟩ :=
        extendFwdLoop_spec (w := w) g x2 j hj f hc2 (hm2 ▸ hS.inp) (hr2.edgeIdx.trans heptr)
          hs_lt hd_lt hsd ht2_2 ht3_2 hlab2 (fun a ha => by rw [hm2]; exact htab_s a ha) hw
      have hr3 := hr3'.trans hr2
      simp only [← he_def] at hrow3 hfr3
      obtain ⟨y, hx4, hc4, he4', hs4', hd4', hsl4, hcl4', hcn4', hrem4', hidx4', hym⟩ :=
        extendPush_spec (w := w) g rDst x3 e.dst S.stack.length (Or.inr rfl)
          hc3 hd_lt hstk_lt (hr3.dst.trans hdst_reg) (hr3.stackLen.trans hS.stack_len) hw
      have hcb_d := tabRow_hi_le_candBase (g := g) hd_lt
      have hstk_mem : HoldsList (stackBase g) (S.stack.reverse ++ [e.dst]) y.mem := by
        have hbase : HoldsList (stackBase g) S.stack.reverse
            (Function.update x3.mem (visBase g + e.dst) 1) :=
          hS.stack_mem.frame fun a ha1 ha2 => by
            rw [Function.update_of_ne (by wram_omega), hfr3 _ (by wram_omega), hm2]
        simpa only [hym, List.length_reverse] using hbase.append_one e.dst
      have hSy : StateAt g (push S e.dst (e.constraint ∘ f)) y :=
        hS.push_slot hc4 hd_lt hgd
          (fun a ha => by
            rw [hym, Function.update_of_ne (by wram_omega), Function.update_of_ne (by wram_omega)]
            exact hrow3 a ha)
          (by rw [hym, Function.update_of_ne (by wram_omega), Function.update_self])
          hstk_mem hsl4 (hcl4'.trans (hr3.compLen.trans hS.comp_len))
          (fun a hnr hnv hns => by
            rw [hym, Function.update_of_ne hns, Function.update_of_ne hnv, hfr3 a hnr, hm2])
      have hex_tot : ExecWithin w extendCode x y (28 * L + 30) :=
        (hx1.seq (ExecWithin.branch_pos hc_outer
          (ExecWithin.branch_pos hc_inner (hx2.seq (hx3.seq hx4))))).mono (by omega)
      refine ⟨y, hex_tot, ?_, he4'.trans (hr3.edgeIdx.trans heptr),
        hs4'.trans (hr3.src.trans hsrc_reg), hd4'.trans (hr3.dst.trans hdst_reg),
        hcn4'.trans hr3.curNode, hrem4'.trans hr3.rem, hidx4'.trans hr3.outerIdx, fun a ha => ?_⟩
      · simpa only [extend, hgs, hgd] using hSy
      · rw [hym, Function.update_of_ne (by wram_omega), Function.update_of_ne (by omega),
          hfr3 _ (by wram_omega), hm2]
    | some h =>
      obtain ⟨hvis_d, _⟩ := hS.vis_some e.dst hd_lt h hgd
      have hc_inner : ¬ (Cond.eq rTmp2 rZero).Holds x1 := by
        simp only [Cond.holds_eq, ht2_1, ← he_def, hvis_d, hc1.zero, Nat.one_ne_zero,
          not_false_eq_true]
      exact retSame (by simp only [extend, hgs, hgd])
        ((hx1.seq (ExecWithin.branch_pos hc_outer (ExecWithin.branch_neg hc_inner hnop))).mono
          (by omega))
  | none =>
    have hvis_s : x.mem (visBase g + e.src) = 0 := hS.vis_none e.src hs_lt hgs
    have hc_outer : ¬ (Cond.eq rTmp1 rOne).Holds x1 := by
      simp only [Cond.holds_eq, ht1_1, ← he_def, hvis_s, hc1.one, Nat.zero_ne_one,
        not_false_eq_true]
    cases hgd : S.get e.dst with
    | some h =>
      obtain ⟨hvis_d, htab_d⟩ := hS.vis_some e.dst hd_lt h hgd
      have hsd : e.src ≠ e.dst := by intro h0; rw [← h0, hgs] at hgd; nomatch hgd
      have hc_inner : (Cond.eq rTmp2 rOne).Holds x1 := by
        simp only [Cond.holds_eq, ht2_1, ← he_def, hvis_d, hc1.one]
      have hstk_lt : S.stack.length < slots g := hstk_of hs_lt hgs
      have hcb_s := tabRow_hi_le_candBase (g := g) hs_lt
      have hcb_d := tabRow_hi_le_candBase (g := g) hd_lt
      obtain ⟨x2, hx2, hc2, hr2', hinv2, hfr2⟩ :=
        invLoops_spec (w := w) g x1 j hj hc1 (hm1 ▸ hS.inp) he1 hw
      have hr2 := hr2'.trans hr1
      simp only [← he_def] at hinv2
      obtain ⟨x3, hx3, hc3, ht2_3, ht3_3, hlab3, hr3', hm3⟩ :=
        extendPrep_spec (w := w) g rDst rSrc x2 e.dst e.src (Or.inr ⟨rfl, rfl⟩)
          hc2 hd_lt hs_lt (hr2.dst.trans hdst_reg) (hr2.src.trans hsrc_reg) hw
      have hr3 := hr3'.trans hr2
      obtain ⟨x4, hx4, hc4, hr4', hrow4, hfr4⟩ :=
        extendBwdLoop_spec (w := w) g x3 j hj h hc3 hs_lt hd_lt hsd ht2_3 ht3_3 hlab3
          (fun a ha => by
            simp only [← he_def]
            rw [hm3, hfr2 _ (by wram_omega), hm1]
            exact htab_d a ha)
          (fun b hb => by simp only [← he_def]; rw [hm3]; exact hinv2 b hb) hw
      have hr4 := hr4'.trans hr3
      simp only [← he_def] at hrow4 hfr4
      obtain ⟨y, hx5, hc5, he5', hs5', hd5', hsl5, hcl5', hcn5', hrem5', hidx5', hym⟩ :=
        extendPush_spec (w := w) g rSrc x4 e.src S.stack.length (Or.inl rfl)
          hc4 hs_lt hstk_lt (hr4.src.trans hsrc_reg) (hr4.stackLen.trans hS.stack_len) hw
      have hstk_mem : HoldsList (stackBase g) (S.stack.reverse ++ [e.src]) y.mem := by
        have hbase : HoldsList (stackBase g) S.stack.reverse
            (Function.update x4.mem (visBase g + e.src) 1) :=
          hS.stack_mem.frame fun a ha1 ha2 => by
            rw [Function.update_of_ne (by wram_omega), hfr4 _ (by wram_omega), hm3,
              hfr2 _ (by wram_omega), hm1]
        simpa only [hym, List.length_reverse] using hbase.append_one e.src
      have hS' : StateAt g S x2 :=
        hS.frame_inv hc2 (hr2.stackLen.trans hS.stack_len) (hr2.compLen.trans hS.comp_len)
          (fun a ha => by rw [hfr2 a ha, hm1])
      have hSy : StateAt g (push S e.src (preimage (List.finRange L) e.constraint ∘ h)) y :=
        hS'.push_slot hc5 hs_lt hgs
          (fun a ha => by
            rw [hym, Function.update_of_ne (by wram_omega), Function.update_of_ne (by wram_omega)]
            exact hrow4 a ha)
          (by rw [hym, Function.update_of_ne (by wram_omega), Function.update_self])
          hstk_mem hsl5 (hcl5'.trans (hr4.compLen.trans hS.comp_len))
          (fun a hnr hnv hns => by
            rw [hym, Function.update_of_ne hns, Function.update_of_ne hnv, hfr4 a hnr, hm3])
      have hex_tot : ExecWithin w extendCode x y (28 * L + 30) :=
        (hx1.seq (ExecWithin.branch_neg hc_outer
          (ExecWithin.branch_pos hc_inner (hx2.seq (hx3.seq (hx4.seq hx5)))))).mono (by omega)
      refine ⟨y, hex_tot, ?_, he5'.trans (hr4.edgeIdx.trans heptr),
        hs5'.trans (hr4.src.trans hsrc_reg), hd5'.trans (hr4.dst.trans hdst_reg),
        hcn5'.trans hr4.curNode, hrem5'.trans hr4.rem, hidx5'.trans hr4.outerIdx, fun a ha => ?_⟩
      · simpa only [extend, hgs, hgd] using hSy
      · rw [hym, Function.update_of_ne (by wram_omega), Function.update_of_ne (by omega),
          hfr4 _ (by wram_omega), hm3, hfr2 _ (by wram_omega), hm1]
    | none =>
      have hvis_d : x.mem (visBase g + e.dst) = 0 := hS.vis_none e.dst hd_lt hgd
      have hc_inner : ¬ (Cond.eq rTmp2 rOne).Holds x1 := by
        simp only [Cond.holds_eq, ht2_1, ← he_def, hvis_d, hc1.one, Nat.zero_ne_one,
          not_false_eq_true]
      exact retSame (by simp only [extend, hgs, hgd])
        ((hx1.seq (ExecWithin.branch_neg hc_outer (ExecWithin.branch_neg hc_inner hnop))).mono
          (by omega))

private theorem pruneCode_spec {L w : ℕ} (g : Graph (Fin L → Fin L)) (S : State (Fin L))
    (x : Data 34) (j : ℕ) (hj : j < g.edges.length)
    (hS : StateAt g S x)
    (heptr : x.regs rEdgeIdx = 4 + j * (L + 2))
    (hsrc_reg : x.regs rSrc = g.edges[j].src)
    (hdst_reg : x.regs rDst = g.edges[j].dst)
    (hw : Fits w (wordBound g)) :
    ∃ y, ExecWithin w pruneCode x y (16 * L + 16) ∧
      StateAt g (prune S g.edges[j]) y ∧
      y.regs rCurNode = x.regs rCurNode ∧ y.regs rRem = x.regs rRem ∧
      y.regs rOuterIdx = x.regs rOuterIdx ∧
      ∀ a < visBase g, y.mem a = x.mem a := by
  set e := g.edges[j] with he_def
  have hs_lt : e.src < slots g := src_lt_slots (List.getElem_mem hj)
  have hd_lt : e.dst < slots g := dst_lt_slots (List.getElem_mem hj)
  have hed := edge_end_le_headBase hj
  obtain ⟨x1, hx1, hc1, ht1_1, ht2_1, hr1, hm1⟩ :=
    edgeVisLoad_spec (w := w) g S x j hj hS hsrc_reg hdst_reg hw
  have hnop : ExecWithin w (.op (.copy rLabIdx rLabIdx)) x1 x1 1 :=
    ⟨1, le_rfl, exec_nop rLabIdx x1⟩
  have hS1 : StateAt g S x1 :=
    hS.of_eq hc1 (hr1.stackLen.trans hS.stack_len) (hr1.compLen.trans hS.comp_len) hm1
  have retSame (hpr : prune S e = S) (hex : ExecWithin w pruneCode x x1 (16 * L + 16)) :
      ∃ y, ExecWithin w pruneCode x y (16 * L + 16) ∧
        StateAt g (prune S e) y ∧
        y.regs rCurNode = x.regs rCurNode ∧ y.regs rRem = x.regs rRem ∧
        y.regs rOuterIdx = x.regs rOuterIdx ∧
        ∀ a < visBase g, y.mem a = x.mem a :=
    ⟨x1, hex, hpr.symm ▸ hS1, hr1.curNode, hr1.rem, hr1.outerIdx, fun a _ => by rw [hm1]⟩
  cases hgs : S.get e.src with
  | none =>
    have hc_outer : ¬ (Cond.eq rTmp1 rOne).Holds x1 := by
      simp only [Cond.holds_eq, ht1_1, ← he_def, hS.vis_none e.src hs_lt hgs, hc1.one,
        Nat.zero_ne_one, not_false_eq_true]
    exact retSame (by simp only [prune, hgs])
      ((hx1.seq (ExecWithin.branch_neg hc_outer hnop)).mono (by omega))
  | some f =>
    obtain ⟨hvis_s, htab_s⟩ := hS.vis_some e.src hs_lt f hgs
    have hc_outer : (Cond.eq rTmp1 rOne).Holds x1 := by
      simp only [Cond.holds_eq, ht1_1, ← he_def, hvis_s, hc1.one]
    cases hgd : S.get e.dst with
    | none =>
      have hc_inner : ¬ (Cond.eq rTmp2 rOne).Holds x1 := by
        simp only [Cond.holds_eq, ht2_1, ← he_def, hS.vis_none e.dst hd_lt hgd, hc1.one,
          Nat.zero_ne_one, not_false_eq_true]
      exact retSame (by simp only [prune, hgs, hgd])
        ((hx1.seq (ExecWithin.branch_pos hc_outer
          (ExecWithin.branch_neg hc_inner hnop))).mono (by omega))
    | some h =>
      obtain ⟨hvis_d, htab_d⟩ := hS.vis_some e.dst hd_lt h hgd
      have hc_inner : (Cond.eq rTmp2 rOne).Holds x1 := by
        simp only [Cond.holds_eq, ht2_1, ← he_def, hvis_d, hc1.one]
      have hcb_s := tabRow_hi_le_candBase (g := g) hs_lt
      have hcb_d := tabRow_hi_le_candBase (g := g) hd_lt
      obtain ⟨x2, hx2, hc2, ht2_2, ht3_2, hlab2, hr2', hm2'⟩ :=
        extendPrep_spec (w := w) g rSrc rDst x1 e.src e.dst (Or.inl ⟨rfl, rfl⟩)
          hc1 hs_lt hd_lt (hr1.src.trans hsrc_reg) (hr1.dst.trans hdst_reg) hw
      have hr2 := hr2'.trans hr1
      have hm2 := hm2'.trans hm1
      let cVal (a : ℕ) : ℕ :=
        if ha : a < L then
          (S.cand ⟨a, ha⟩ && decide (e.constraint (f ⟨a, ha⟩) = h ⟨a, ha⟩)).toNat
        else 0
      let P (k : ℕ) (z : Data 34) : Prop :=
        ConstRegs g z ∧ z.regs rTmp2 = tabBase g + e.src * L ∧
        z.regs rTmp3 = tabBase g + e.dst * L ∧ Phase3Regs x z ∧
        (∀ a < k, z.mem (candBase g + a) = cVal a) ∧
        ∀ addr, ¬ (candBase g ≤ addr ∧ addr < candBase g + k) → z.mem addr = x.mem addr
      obtain ⟨y, hx3, ⟨hyC, _, _, hyR, hyCand, hyFr⟩, _⟩ :=
        ExecWithin.loop_count (w := w) (index := rLabIdx) (limit := rL) (body := pruneBody)
          (N := L) (T := 14) P
          (fun z hz => hz.1.regL)
          (fun z hz hk => by
            obtain ⟨hzC, hzT2, hzT3, hzR, hzCand, hzFr⟩ := hz
            set k := z.regs rLabIdx
            have hk_reg : z.regs rLabIdx = k := rfl
            have hzE : z.regs rEdgeIdx = 4 + j * (L + 2) := hzR.edgeIdx.trans heptr
            have hck_mem : z.mem (candBase g + k) = (S.cand ⟨k, hk⟩).toNat := by
              rw [hzFr _ (by omega)]; exact hS.cand_mem k hk
            have : Fits w (candBase g + k) := fits_top hw (by wram_omega)
            have : Fits w (k + 1) := fits_top hw (by wram_omega)
            cases hck : S.cand ⟨k, hk⟩ with
            | false =>
              have hck0 : (S.cand ⟨k, hk⟩).toNat = 0 := by simp only [hck, Bool.toNat_false]
              unfold pruneBody
              wram_exec [hzC.one, hzC.candB, hk_reg, hck_mem, hck0]
              refine ⟨⟨by wram_simp [hzC], by wram_simp [hzT2], by wram_simp [hzT3],
                by wram_simp [hzR], ?_, ?_⟩, by wram_simp⟩
              · simp only [Data.set_mem]
                intro a ha
                by_cases hak : a = k
                · subst hak; rw [hck_mem, hck0]
                  simp only [cVal, hk, ↓reduceDIte, hck, Bool.false_and, Bool.toNat_false]
                · exact hzCand a (by omega)
              · simp only [Data.set_mem]; exact fun addr haddr => hzFr addr (by omega)
            | true =>
              have hck1 : (S.cand ⟨k, hk⟩).toNat = 1 := by simp only [hck, Bool.toNat_true]
              have hfk_lt := (f ⟨k, hk⟩).isLt
              have hfa : z.mem (tabBase g + e.src * L + k) = (f ⟨k, hk⟩).val := by
                rw [hzFr _ (by omega)]; exact htab_s k hk
              have hha : z.mem (tabBase g + e.dst * L + k) = (h ⟨k, hk⟩).val := by
                rw [hzFr _ (by omega)]; exact htab_d k hk
              have hcfa : z.mem (4 + j * (L + 2) + ((f ⟨k, hk⟩).val + 2)) =
                  (e.constraint (f ⟨k, hk⟩)).val := by
                rw [hzFr _ (by wram_omega),
                  show 4 + j * (L + 2) + ((f ⟨k, hk⟩).val + 2) =
                    4 + j * (L + 2) + 2 + (f ⟨k, hk⟩).val by omega]
                exact hS.inp.edge_val j hj (f ⟨k, hk⟩).val hfk_lt
              have : Fits w (tabBase g + e.src * L + k) := fits_top hw (by wram_omega)
              have : Fits w (tabBase g + e.dst * L + k) := fits_top hw (by wram_omega)
              have : Fits w ((f ⟨k, hk⟩).val + 2) := fits_top hw (by wram_omega)
              have : Fits w (4 + j * (L + 2) + ((f ⟨k, hk⟩).val + 2)) := fits_top hw (by wram_omega)
              by_cases heq_val : (e.constraint (f ⟨k, hk⟩)).val = (h ⟨k, hk⟩).val
              · have heq_fin : e.constraint (f ⟨k, hk⟩) = h ⟨k, hk⟩ := Fin.ext heq_val
                unfold pruneBody
                wram_exec [hzC.one, hzC.two, hzC.candB, hzT2, hzT3, hzE, hk_reg, hck_mem, hck1,
                  hfa, hha, hcfa, heq_val]
                refine ⟨⟨by wram_simp [hzC], by wram_simp [hzT2], by wram_simp [hzT3],
                  by wram_simp [hzR], ?_, ?_⟩, by wram_simp⟩
                · simp only [Data.set_mem]
                  intro a ha
                  by_cases hak : a = k
                  · subst hak; rw [hck_mem, hck1]
                    simp only [cVal, hk, ↓reduceDIte, hck, heq_fin, decide_true, Bool.and_self,
                      Bool.toNat_true]
                  · exact hzCand a (by omega)
                · simp only [Data.set_mem]; exact fun addr haddr => hzFr addr (by omega)
              · have hne_fin : e.constraint (f ⟨k, hk⟩) ≠ h ⟨k, hk⟩ :=
                  fun heq => heq_val (congrArg Fin.val heq)
                have hpws := prefix_write_step hzCand hzFr
                  (show Function.update z.mem (candBase g + k) 0 =
                    Function.update z.mem (candBase g + k) (cVal k) by
                    simp only [cVal, hk, ↓reduceDIte, hck, decide_eq_false hne_fin,
                      Bool.true_and, Bool.toNat_false])
                unfold pruneBody
                wram_exec [hzC.zero, hzC.one, hzC.two, hzC.candB, hzT2, hzT3, hzE, hk_reg,
                  hck_mem, hck1, hfa, hha, hcfa, heq_val]
                refine ⟨⟨by wram_simp [hzC], by wram_simp [hzT2], by wram_simp [hzT3],
                  by wram_simp [hzR], ?_, ?_⟩, by wram_simp⟩
                · simp only [Data.write_mem, Data.set_mem]; exact hpws.1
                · simp only [Data.write_mem, Data.set_mem]; exact hpws.2)
          (by rw [hlab2]; exact Nat.zero_le _)
          (by rw [hlab2]; exact ⟨hc2, ht2_2, ht3_2, hr2,
            fun _ h => by omega, fun addr _ => congrFun hm2 addr⟩)
      rw [hlab2, Nat.sub_zero] at hx3
      have hfr_below : ∀ a < candBase g, y.mem a = x.mem a := fun a ha => hyFr a (by omega)
      have hfr_low : ∀ a < visBase g, y.mem a = x.mem a := fun a ha =>
        hfr_below a (by wram_omega)
      refine ⟨y, (hx1.seq (ExecWithin.branch_pos hc_outer
          (ExecWithin.branch_pos hc_inner (hx2.seq hx3)))).mono (by omega),
        ?_, hyR.curNode, hyR.rem, hyR.outerIdx, hfr_low⟩
      have hpr_eq : prune S e =
          { S with cand := fun a => S.cand a && decide (e.constraint (f a) = h a) } := by
        simp only [prune, hgs, hgd]
      rw [hpr_eq]
      refine ⟨hS.toTableStateAt.frame hyC rfl (candBase g) (by wram_omega) hfr_below,
        by rw [← hpr_eq]; exact (step_prune S e).potential_le.trans hS.pot_le,
        fun a ha => by simpa only [cVal, ha, ↓reduceDIte] using hyCand a ha,
        hyR.stackLen.trans hS.stack_len, hS.stack_lt,
        hS.stack_mem.frame (fun a ha1 _ => hyFr a (by wram_omega)),
        hyR.compLen.trans hS.comp_len, hS.comp_le, hS.comp_lt,
        hS.comp_mem.frame (fun a ha1 _ => hyFr a (by wram_omega))⟩

private abbrev visitPass (L : ℕ) : ℕ := 44 * L + 56
private abbrev freezePass (L : ℕ) : ℕ := 5 * L + 22

private theorem visitListLoop_spec {L w : ℕ} (g : Graph (Fin L → Fin L))
    (es : List (Edge (Fin L → Fin L))) (S : State (Fin L)) (x : Data 34)
    (hS : StateAt g S x) (hch : AdjChain g x.mem (visBase g) (x.regs rCurNode) es)
    (hw : Fits w (wordBound g)) :
    ∃ y, ExecWithin w visitListLoop x y (visitPass L * es.length + 2) ∧
      StateAt g (es.foldl (visit (List.finRange L)) S) y ∧
      y.regs rRem = x.regs rRem ∧ y.regs rOuterIdx = x.regs rOuterIdx := by
  have hwb := outBaseAddr_lt_wordBound g
  induction es generalizing S x with
  | nil =>
    have hcn0 : x.regs rCurNode = 0 := by
      have : ∀ p l, AdjChain g x.mem (visBase g) p l → l = [] → p = 0 := by
        rintro _ _ (_ | _) ⟨⟩; rfl
      exact this _ _ hch rfl
    exact ⟨x, ⟨2, by omega, .loop_exit
        (by simp only [Cond.holds_lt, hS.consts.zero, hcn0]; omega)⟩, hS, rfl, rfl⟩
  | cons e es' ih =>
    have hex_cons : ∃ (p j : ℕ) (hj : j < g.edges.length),
        x.regs rCurNode = p ∧ e = g.edges[j] ∧
        nodeBase g ≤ p ∧ p + 2 ≤ visBase g ∧ x.mem p = j ∧
        AdjChain g x.mem (visBase g) (x.mem (p + 1)) es' := by
      have : ∀ p l, AdjChain g x.mem (visBase g) p l → ∀ d ds, l = d :: ds →
          ∃ (j : ℕ) (hj : j < g.edges.length), d = g.edges[j] ∧
            nodeBase g ≤ p ∧ p + 2 ≤ visBase g ∧ x.mem p = j ∧
            AdjChain g x.mem (visBase g) (x.mem (p + 1)) ds := by
        rintro _ _ (_ | ⟨hj, hlo, hhi, hp0, htl⟩) _ _ ⟨⟩
        exact ⟨_, hj, rfl, hlo, hhi, hp0, htl⟩
      obtain ⟨j, hj, hd, hlo, hhi, hp0, htl⟩ := this _ _ hch e es' rfl
      exact ⟨x.regs rCurNode, j, hj, rfl, hd, hlo, hhi, hp0, htl⟩
    obtain ⟨p, j, hj, hp_reg, rfl, hlo, hhi, hp0, htl⟩ := hex_cons
    have hc_loop : (Cond.lt rZero rCurNode).Holds x := by
      simp only [Cond.holds_lt, hS.consts.zero, hp_reg]
      simp only [nodeBase, headBase] at hlo
      omega
    have hhead : ∃ x1, ExecWithin w visitListHead x x1 8 ∧
        StateAt g S x1 ∧ x1.regs rCurNode = x.mem (p + 1) ∧
        x1.regs rEdgeIdx = 4 + j * (L + 2) ∧
        x1.regs rSrc = g.edges[j].src ∧ x1.regs rDst = g.edges[j].dst ∧
        x1.regs rRem = x.regs rRem ∧ x1.regs rOuterIdx = x.regs rOuterIdx ∧
        x1.mem = x.mem := by
      have hed := edge_end_le_wordBound hj
      have : Fits w (p + 1) := fits_top hw (by wram_omega)
      have : Fits w (j * (L + 2)) := hw.of_le (by omega)
      have : Fits w (4 + j * (L + 2)) := hw.of_le (by omega)
      have : Fits w (4 + j * (L + 2) + 1) := hw.of_le (by omega)
      unfold visitListHead
      wram_exec [hS.consts.one, hS.consts.stride, hS.consts.edgeB, hp_reg, hp0,
        hS.inp.edge_src j hj, hS.inp.edge_dst j hj]
      exact ⟨hS.of_eq (by wram_simp [hS.consts]) (by wram_simp [hS.stack_len])
          (by wram_simp [hS.comp_len]) (by wram_simp),
        by wram_simp, by wram_simp, by wram_simp, by wram_simp, by wram_simp, by wram_simp,
        by wram_simp⟩
    obtain ⟨x1, hx1, hS1, hcn1, he1, hs1, hd1, hrem1, hidx1, hm1⟩ := hhead
    obtain ⟨x2, hx2, hS2, he2, hs2, hd2, hcn2, hrem2, hidx2, hfr2⟩ :=
      extendCode_spec (w := w) g S x1 j hj hS1 he1 hs1 hd1 hw
    obtain ⟨x3, hx3, hS3, hcn3, hrem3, hidx3, hfr3⟩ :=
      pruneCode_spec (w := w) g (extend (List.finRange L) S g.edges[j]) x2 j hj hS2 he2 hs2 hd2 hw
    have hbody_exec : ExecWithin w visitListBody x x3 (44 * L + 54) :=
      (hx1.seq (hx2.seq hx3)).mono (by omega)
    have htl_x3 : AdjChain g x3.mem (visBase g) (x3.regs rCurNode) es' := by
      rw [hcn3, hcn2, hcn1]
      exact htl.frame le_rfl fun a _ ha => by rw [hfr3 a ha, hfr2 a ha, hm1]
    obtain ⟨y, hy, hSy, hremy, hidxy⟩ :=
      ih (visit (List.finRange L) S g.edges[j]) x3 hS3 htl_x3
    obtain ⟨tb, htb, hexb⟩ := hbody_exec
    obtain ⟨tl, htl_t, hexl⟩ := hy
    refine ⟨y, ⟨tb + tl + 2, ?_, .loop_iter hc_loop hexb hexl⟩, hSy,
      hremy.trans (hrem3.trans (hrem2.trans hrem1)),
      hidxy.trans (hidx3.trans (hidx2.trans hidx1))⟩
    simp only [visitPass, List.length_cons, Nat.mul_succ] at htl_t ⊢
    omega

private def weightRAM {L : ℕ} (g : Graph (Fin L → Fin L)) (v : ℕ) : ℕ :=
  16 + freezePass L + visitPass L * (adj g v).length

private def creditRAM {L : ℕ} (g : Graph (Fin L → Fin L)) (S : State (Fin L)) : ℕ :=
  S.wpot (weightRAM g) + freezePass L * S.comp.length

private theorem scanCode_spec {L w : ℕ} (g : Graph (Fin L → Fin L)) (S : State (Fin L))
    (x : Data 34) {u : ℕ} {rest : List ℕ} (hS : StateAt g S x)
    (hst : S.stack = u :: rest) (hcomp_lt : S.comp.length < slots g)
    (hw : Fits w (wordBound g)) :
    ∃ y t, Exec w scanCode x y t ∧
      t + 5 + creditRAM g (scan (List.finRange L) g S) ≤ creditRAM g S ∧
      StateAt g (scan (List.finRange L) g S) y ∧
      y.regs rRem = x.regs rRem ∧ y.regs rOuterIdx = x.regs rOuterIdx := by
  have hu_lt : u < slots g := hS.stack_lt u (by simp only [hst, List.mem_cons, true_or])
  have hstk_split : HoldsList (stackBase g) rest.reverse x.mem ∧
      x.mem (stackBase g + rest.length) = u := by
    have hrev : S.stack.reverse = rest.reverse ++ [u] := by
      simp only [hst, List.reverse_cons]
    have hm := hS.stack_mem
    rw [hrev] at hm
    obtain ⟨h1, h2⟩ := holdsList_append_iff.mp hm
    rw [List.length_reverse] at h2
    exact ⟨h1, (holdsList_cons_iff.mp h2).1⟩
  have hrest_le : rest.length < slots g := by
    have hp := hS.pot_le
    unfold State.potential at hp
    simp only [hst, List.length_cons] at hp
    omega
  set S1 : State (Fin L) := { S with stack := rest, comp := u :: S.comp }
  have hpop_raw : ∃ x1, ExecWithin w scanPop x x1 8 ∧
      ConstRegs g x1 ∧ x1.regs rStackLen = rest.length ∧
      x1.regs rCompLen = S.comp.length + 1 ∧
      x1.regs rCurNode = x.mem (headBase g + u) ∧
      x1.regs rRem = x.regs rRem ∧ x1.regs rOuterIdx = x.regs rOuterIdx ∧
      x1.mem = Function.update x.mem (compBase g + S.comp.length) u := by
    have hlen_u : x.regs rStackLen = rest.length + 1 := by
      simp only [hS.stack_len, hst, List.length_cons]
    have : Fits w (stackBase g + rest.length) := fits_top hw (by wram_omega)
    have : Fits w (compBase g + S.comp.length) := fits_top hw (by wram_omega)
    have : Fits w (S.comp.length + 1) := fits_top hw (by wram_omega)
    have : Fits w (headBase g + u) := fits_top hw (by wram_omega)
    have hfr_hb : Function.update x.mem (compBase g + S.comp.length) u (headBase g + u) =
        x.mem (headBase g + u) := Function.update_of_ne (by wram_omega) _ _
    unfold scanPop
    wram_exec [hS.consts.one, hS.consts.headB, hS.consts.stackB, hS.consts.compB,
      hlen_u, Nat.add_sub_cancel rest.length 1, hstk_split.2, hS.comp_len, hfr_hb]
    exact ⟨by wram_simp [hS.consts], by wram_simp, by wram_simp, by wram_simp [hfr_hb],
      by wram_simp, by wram_simp, by wram_simp⟩
  obtain ⟨x1, hx1, hc1, hsl1, hcl1, hcn1, hrem1, hidx1, hx1m⟩ := hpop_raw
  have hfr_comp : ∀ a < compBase g, x1.mem a = x.mem a := fun a ha => by
    rw [hx1m]; exact Function.update_of_ne (by omega) _ _
  have hfr_low : ∀ a < visBase g, x1.mem a = x.mem a := fun a ha => hfr_comp a (by wram_omega)
  have hS1 : StateAt g S1 x1 := by
    have hcm1 : HoldsList (compBase g) S1.comp.reverse x1.mem := by
      have hbase := hS.comp_mem.append_one u
      rw [List.length_reverse] at hbase
      simpa only [S1, List.reverse_cons, hx1m] using hbase
    exact ⟨hS.toTableStateAt.frame hc1 rfl (compBase g) (by wram_omega) hfr_comp,
      (by
        have hp := hS.pot_le
        have hun : S1.unvisited = S.unvisited := rfl
        unfold State.potential at hp ⊢
        simp only [S1, hun, hst, List.length_cons] at hp ⊢
        omega),
      (fun a ha => by rw [hfr_comp _ (by wram_omega)]; exact hS.cand_mem a ha),
      hsl1,
      (fun v hv => hS.stack_lt v (by simp only [hst, List.mem_cons]; exact Or.inr hv)),
      (hstk_split.1.frame fun a _ ha2 => by
        rw [List.length_reverse] at ha2; exact hfr_comp a (by wram_omega)),
      (by simpa only [S1, List.length_cons] using hcl1),
      (by simp only [S1, List.length_cons]; omega),
      (fun v hv => by
        rcases List.mem_cons.mp hv with rfl | hv <;> [exact hu_lt; exact hS.comp_lt v hv]),
      hcm1⟩
  have hch1 : AdjChain g x1.mem (visBase g) (x1.regs rCurNode) (adj g u) := by
    rw [hcn1]
    exact (hS.bkt u hu_lt).frame le_rfl fun a _ ha => hfr_low a ha
  obtain ⟨y, hx2, hSy, hrem2, hidx2⟩ := visitListLoop_spec (w := w) g (adj g u) S1 x1 hS1 hch1 hw
  obtain ⟨t1, ht1, hex1⟩ := hx1
  obtain ⟨t2, ht2, hex2⟩ := hx2
  rw [scan_cons (List.finRange L) g hst]
  refine ⟨y, t1 + t2, hex1.seq hex2, ?_, hSy, hrem2.trans hrem1, hidx2.trans hidx1⟩
  have hstep := foldl_visit_step (List.finRange L) (adj g u) (S := S1) (adj_bounds hS.len_table u)
  have hw_pot := hstep.wpot (weightRAM g)
  have hS1w : S1.wpot (weightRAM g) + weightRAM g u = S.wpot (weightRAM g) := by
    have hun : S1.unvisited = S.unvisited := rfl
    simp only [State.wpot, hun, S1, hst, List.map_cons, List.sum_cons]
    omega
  have hwu : weightRAM g u = 16 + freezePass L + visitPass L * (adj g u).length := rfl
  unfold creditRAM
  dsimp only [S1] at hstep hw_pot hS1w ⊢
  rw [hstep.comp]
  simp only [List.length_cons, Nat.mul_succ]
  omega

private theorem exploreCode_spec {L w : ℕ} (g : Graph (Fin L → Fin L)) (S : State (Fin L))
    (x : Data 34) (hS : StateAt g S x) (hcomp0 : S.comp = [])
    (hw : Fits w (wordBound g)) :
    ∃ y t, Exec w exploreCode x y t ∧
      t + creditRAM g ((scan (List.finRange L) g)^[slots g] S) ≤ creditRAM g S + 8 ∧
      StateAt g ((scan (List.finRange L) g)^[slots g] S) y ∧
      y.regs rOuterIdx = x.regs rOuterIdx := by
  have hset : ∃ x0, ExecWithin w (ram[ rRem ← rN ] : Code .standard 34) x x0 1 ∧
      StateAt g S x0 ∧ x0.regs rRem = slots g ∧ x0.regs rOuterIdx = x.regs rOuterIdx := by
    wram_exec [hS.consts.regN]
    exact ⟨hS.of_eq (by wram_simp [hS.consts]) (by wram_simp [hS.stack_len])
        (by wram_simp [hS.comp_len]) (by wram_simp),
      by wram_simp, by wram_simp⟩
  obtain ⟨x0, ⟨t0, ht0, hex0⟩, hS0, hrem0, hidx0⟩ := hset
  suffices hloop : ∀ (k : ℕ) (S' : State (Fin L)) (z : Data 34),
      StateAt g S' z → z.regs rRem = k → S'.comp.length + k ≤ slots g →
      ∃ y t, Exec w (.loop (.lt rZero rRem) exploreBody) z y t ∧
        t + creditRAM g ((scan (List.finRange L) g)^[k] S') ≤ creditRAM g S' + 7 ∧
        StateAt g ((scan (List.finRange L) g)^[k] S') y ∧
        y.regs rOuterIdx = z.regs rOuterIdx by
    obtain ⟨y, t, hexl, hcred, hSy, hidxy⟩ :=
      hloop (slots g) S x0 hS0 hrem0 (by simp only [hcomp0, List.length_nil, Nat.zero_add, le_refl])
    exact ⟨y, t0 + t, hex0.seq hexl, by omega, hSy, hidxy.trans hidx0⟩
  intro k
  induction k with
  | zero =>
    intro S' z hS' hrem' _
    refine ⟨z, 2, .loop_exit (by simp only [Cond.holds_lt, hS'.consts.zero, hrem']; omega),
      by simp only [Function.iterate_zero, id_eq]; omega, hS', rfl⟩
  | succ k ih =>
    intro S' z hS' hrem' hck
    have hc_loop : (Cond.lt rZero rRem).Holds z := by
      simp only [Cond.holds_lt, hS'.consts.zero, hrem']; omega
    cases hst : S'.stack with
    | nil =>
      have hc_br : (Cond.eq rStackLen rZero).Holds z := by
        simp only [Cond.holds_eq, hS'.stack_len, hst, List.length_nil, hS'.consts.zero]
      have hbody_nil : ∃ z1, ExecWithin w (ram[ rRem ← rZero ] : Code .standard 34) z z1 1 ∧
          StateAt g S' z1 ∧ z1.regs rRem = 0 ∧ z1.regs rOuterIdx = z.regs rOuterIdx := by
        wram_exec [hS'.consts.zero]
        exact ⟨hS'.of_eq (by wram_simp [hS'.consts]) (by wram_simp [hS'.stack_len])
            (by wram_simp [hS'.comp_len]) (by wram_simp),
          by wram_simp, by wram_simp⟩
      obtain ⟨z1, ⟨tb, htb, hexb⟩, hS1, hrem1, hidx1⟩ := hbody_nil
      have hexl_exit : Exec w (.loop (.lt rZero rRem) exploreBody) z1 z1 2 :=
        .loop_exit (by simp only [Cond.holds_lt, hS1.consts.zero, hrem1]; omega)
      have hfix : (scan (List.finRange L) g)^[k + 1] S' = S' :=
        Function.iterate_fixed (scan_nil (List.finRange L) g hst) (k + 1)
      rw [hfix]
      exact ⟨z1, (tb + 1) + 2 + 2,
        .loop_iter hc_loop (.branch_pos hc_br hexb) hexl_exit, by omega, hS1, hidx1⟩
    | cons u rest =>
      have hc_br : ¬ (Cond.eq rStackLen rZero).Holds z := by
        simp only [Cond.holds_eq, hS'.stack_len, hst, List.length_cons, hS'.consts.zero,
          Nat.add_one_ne_zero, not_false_eq_true]
      have hdec : ∃ z1, ExecWithin w (ram[ rRem ← rRem - rOne ] : Code .standard 34) z z1 1 ∧
          StateAt g S' z1 ∧ z1.regs rRem = k ∧ z1.regs rOuterIdx = z.regs rOuterIdx := by
        have : Fits w k := hw.of_le (by have := edges_lt_wordBound g; omega)
        wram_exec [hS'.consts.one, hrem']
        exact ⟨hS'.of_eq (by wram_simp [hS'.consts]) (by wram_simp [hS'.stack_len])
            (by wram_simp [hS'.comp_len]) (by wram_simp),
          by wram_simp, by wram_simp⟩
      obtain ⟨z1, ⟨td, htd, hexd⟩, hS1, hrem1, hidx1⟩ := hdec
      obtain ⟨z2, ts, hexs, hcred_s, hS2, hrem2, hidx2⟩ :=
        scanCode_spec (w := w) g S' z1 hS1 hst (by omega) hw
      have hcomp_next : (scan (List.finRange L) g S').comp.length = S'.comp.length + 1 := by
        rw [scan_cons (List.finRange L) g hst]
        have hstep := foldl_visit_step (List.finRange L) (adj g u)
          (S := { S' with stack := rest, comp := u :: S'.comp }) (adj_bounds hS'.len_table u)
        rw [hstep.comp]; rfl
      obtain ⟨y, tl, hexl, hcred_l, hSy, hidxy⟩ :=
        ih (scan (List.finRange L) g S') z2 hS2 (hrem2.trans hrem1) (by omega)
      rw [Function.iterate_succ_apply]
      exact ⟨y, (td + ts + 2) + tl + 2,
        .loop_iter hc_loop (.branch_neg hc_br (hexd.seq hexs)) hexl,
        by omega, hSy, hidxy.trans (hidx2.trans hidx1)⟩

private theorem settleCode_spec {L w : ℕ} [NeZero L] (g : Graph (Fin L → Fin L))
    (S : State (Fin L)) (x : Data 34) (hS : StateAt g S x) (hw : Fits w (wordBound g)) :
    ∃ y, ExecWithin w settleCode x y ((11 * L + 10) + freezePass L * S.comp.length) ∧
      TableStateAt g (settle (List.finRange L) S) y ∧
      y.regs rOuterIdx = x.regs rOuterIdx := by
  have hpick_init : ∃ x1, ExecWithin w settlePickInit x x1 3 ∧
      ConstRegs g x1 ∧ x1.regs rChosen = 0 ∧ x1.regs rTmp3 = 0 ∧ x1.regs rLabIdx = 0 ∧
      x1.regs rCompLen = S.comp.length ∧ x1.regs rOuterIdx = x.regs rOuterIdx ∧
      x1.mem = x.mem := by
    unfold settlePickInit
    wram_exec [hS.consts.zero]
    exact ⟨by wram_simp [hS.consts], by wram_simp, by wram_simp, by wram_simp,
      by wram_simp [hS.comp_len], by wram_simp, by wram_simp⟩
  obtain ⟨x1, hx1, hc1, hch1, ht3_1, hlab1, hcl1, hidx1, hm1⟩ := hpick_init
  let optAt (k : ℕ) : Option (Fin L) := ((List.finRange L).take k).find? S.cand
  let Ppick (k : ℕ) (z : Data 34) : Prop :=
    ConstRegs g z ∧ z.regs rCompLen = S.comp.length ∧ z.regs rOuterIdx = x.regs rOuterIdx ∧
    z.mem = x.mem ∧
    match optAt k with
    | none => z.regs rTmp3 = 0 ∧ z.regs rChosen = 0
    | some c => z.regs rTmp3 = 1 ∧ z.regs rChosen = c.val
  obtain ⟨x2, hx2, ⟨hc2, hcl2, hidx2, hm2, hopt2⟩, _⟩ :=
    ExecWithin.loop_count (w := w) (index := rLabIdx) (limit := rL) (body := pickChosenBody)
      (N := L) (T := 9) Ppick
      (fun z hz => hz.1.regL)
      (fun z hz hk => by
        obtain ⟨hzC, hzCL, hzIdx, hzMem, hzOpt⟩ := hz
        set k := z.regs rLabIdx
        have hk_reg : z.regs rLabIdx = k := rfl
        have htake_succ : (List.finRange L).take (k + 1) =
            (List.finRange L).take k ++ [⟨k, hk⟩] := by
          rw [List.take_succ_eq_append_getElem (by simp only [List.length_finRange]; exact hk),
            List.getElem_finRange]
          rfl
        have : Fits w (candBase g + k) := fits_top hw (by wram_omega)
        have : Fits w (k + 1) := fits_top hw (by wram_omega)
        cases hok : optAt k with
        | some c =>
          rw [hok] at hzOpt
          have hnext : optAt (k + 1) = some c := by
            simp only [optAt, htake_succ, List.find?_append,
              show ((List.finRange L).take k).find? S.cand = some c from hok, Option.some_or]
          unfold pickChosenBody
          wram_exec [hzC.zero, hzC.one, hk_reg, hzOpt.1]
          refine ⟨⟨by wram_simp [hzC], by wram_simp [hzCL], by wram_simp [hzIdx],
            by wram_simp [hzMem], ?_⟩, by wram_simp⟩
          rw [hnext]; exact ⟨by wram_simp [hzOpt.1], by wram_simp [hzOpt.2]⟩
        | none =>
          rw [hok] at hzOpt
          have hck_mem : z.mem (candBase g + k) = (S.cand ⟨k, hk⟩).toNat := by
            rw [hzMem]; exact hS.cand_mem k hk
          cases hck : S.cand ⟨k, hk⟩ with
          | true =>
            have hck1 : (S.cand ⟨k, hk⟩).toNat = 1 := by simp only [hck, Bool.toNat_true]
            have hnext : optAt (k + 1) = some ⟨k, hk⟩ := by
              simp only [optAt, htake_succ, List.find?_append,
                show ((List.finRange L).take k).find? S.cand = none from hok, Option.none_or,
                List.find?_cons, hck]
            unfold pickChosenBody
            wram_exec [hzC.zero, hzC.one, hzC.candB, hk_reg, hzOpt.1, hck_mem, hck1]
            refine ⟨⟨by wram_simp [hzC], by wram_simp [hzCL], by wram_simp [hzIdx],
              by wram_simp [hzMem], ?_⟩, by wram_simp⟩
            rw [hnext]; exact ⟨by wram_simp, by wram_simp⟩
          | false =>
            have hck0 : (S.cand ⟨k, hk⟩).toNat = 0 := by simp only [hck, Bool.toNat_false]
            have hnext : optAt (k + 1) = none := by
              simp only [optAt, htake_succ, List.find?_append,
                show ((List.finRange L).take k).find? S.cand = none from hok, Option.none_or,
                List.find?_cons, hck, List.find?_nil]
            unfold pickChosenBody
            wram_exec [hzC.zero, hzC.one, hzC.candB, hk_reg, hzOpt.1, hck_mem, hck0]
            refine ⟨⟨by wram_simp [hzC], by wram_simp [hzCL], by wram_simp [hzIdx],
              by wram_simp [hzMem], ?_⟩, by wram_simp⟩
            rw [hnext]; exact ⟨by wram_simp [hzOpt.1], by wram_simp [hzOpt.2]⟩)
      (by rw [hlab1]; exact Nat.zero_le _)
      (by rw [hlab1]; refine ⟨hc1, hcl1, hidx1, hm1, ?_⟩
          simp only [optAt, List.take_zero, List.find?_nil, ht3_1, hch1, and_self])
  rw [hlab1, Nat.sub_zero] at hx2
  set chosen : Fin L := ((List.finRange L).find? S.cand).getD default
  have hchosen_reg : x2.regs rChosen = chosen.val := by
    have htakeL : (List.finRange L).take L = List.finRange L :=
      List.take_of_length_le (by simp only [List.length_finRange, le_rfl])
    simp only [optAt, htakeL] at hopt2
    cases hfind : (List.finRange L).find? S.cand <;>
    · rw [hfind] at hopt2
      simp only [chosen, hfind, Option.getD_none, Option.getD_some]
      exact hopt2.2
  have hrem_init : ∃ x3, ExecWithin w (ram[ rRem ← rZero ] : Code .standard 34) x2 x3 1 ∧
      TableStateAt g S x3 ∧ x3.regs rChosen = chosen.val ∧ x3.regs rRem = 0 ∧
      x3.regs rCompLen = S.comp.length ∧ x3.regs rOuterIdx = x.regs rOuterIdx ∧
      HoldsList (compBase g) S.comp.reverse x3.mem := by
    wram_exec [hc2.zero]
    exact ⟨hS.toTableStateAt.of_eq (by wram_simp [hc2]) (by wram_simp [hm2]),
      by wram_simp [hchosen_reg], by wram_simp, by wram_simp [hcl2], by wram_simp [hidx2],
      by simp only [Data.set_mem, hm2]; exact hS.comp_mem⟩
  obtain ⟨x3, hx3, hT3, hch3, hrem3, hcl3, hidx3, hcm3⟩ := hrem_init
  let tabAt (k : ℕ) := (S.comp.take k).foldl
    (fun t v => t.set v (freeze chosen (t.getD v none))) S.table
  let Pfrz (k : ℕ) (z : Data 34) : Prop :=
    TableStateAt g { S with table := tabAt k } z ∧
    z.regs rChosen = chosen.val ∧ z.regs rCompLen = S.comp.length ∧
    z.regs rOuterIdx = x.regs rOuterIdx ∧
    HoldsList (compBase g) S.comp.reverse z.mem
  obtain ⟨x4, hx4, ⟨hT4, _, _, hidx4, _⟩, _⟩ :=
    ExecWithin.loop_count (w := w) (index := rRem) (limit := rCompLen) (body := freezeCompBody)
      (N := S.comp.length) (T := 5 * L + 20) Pfrz
      (fun z hz => hz.2.2.1)
      (fun z hz hk => by
        obtain ⟨hzT, hzCh, hzCL, hzIdx, hzCM⟩ := hz
        set k := z.regs rRem
        have hk_reg : z.regs rRem = k := rfl
        set v := S.comp[k]
        have hv_lt : v < slots g := hS.comp_lt v (List.getElem_mem hk)
        have hv_cb := tabRow_hi_le_candBase (g := g) hv_lt
        have hcomp_le := hS.comp_le
        have hrev_get : z.mem (compBase g + (S.comp.length - 1 - k)) = v := by
          have hg := hzCM.get (S.comp.length - 1 - k) (by rw [List.length_reverse]; omega)
          rw [List.getElem_reverse] at hg
          simpa only [show S.comp.length - 1 - (S.comp.length - 1 - k) = k by omega] using hg
        have htab_next : tabAt (k + 1) =
            (tabAt k).set v (freeze chosen ((tabAt k).getD v none)) := by
          simp only [tabAt]
          rw [List.take_succ_eq_append_getElem hk, List.foldl_append, List.foldl_cons,
            List.foldl_nil]
        have : Fits w (compBase g + (S.comp.length - 1 - k)) := fits_top hw (by wram_omega)
        have : Fits w (visBase g + v) := fits_top hw (by wram_omega)
        have : Fits w (k + 1) := fits_top hw (by wram_omega)
        have hload_v : ∃ z1, ExecWithin w freezeLoadV z z1 6 ∧
            ConstRegs g z1 ∧ z1.regs rSrc = v ∧ z1.regs rTmp1 = z.mem (visBase g + v) ∧
            z1.regs rChosen = chosen.val ∧ z1.regs rRem = k ∧
            z1.regs rCompLen = S.comp.length ∧ z1.regs rOuterIdx = x.regs rOuterIdx ∧
            z1.mem = z.mem := by
          unfold freezeLoadV
          wram_exec [hzT.consts.one, hzT.consts.compB, hzT.consts.visB, hzCL, hk_reg, hrev_get]
          exact ⟨by wram_simp [hzT.consts], by wram_simp, by wram_simp, by wram_simp [hzCh],
            by wram_simp [hk_reg], by wram_simp [hzCL], by wram_simp [hzIdx], by wram_simp⟩
        obtain ⟨z1, hz1_ex, hz1C, hz1S, hz1T1, hz1Ch, hz1Rem, hz1CL, hz1Idx, hz1m⟩ := hload_v
        cases hgv : ({ S with table := tabAt k } : State (Fin L)).get v with
        | none =>
          have hvis0 : z.mem (visBase g + v) = 0 := hzT.vis_none v hv_lt hgv
          have hc_br : ¬ (Cond.eq rTmp1 rOne).Holds z1 := by
            simp only [Cond.holds_eq, hz1T1, hvis0, hz1C.one, Nat.zero_ne_one, not_false_eq_true]
          have hnop_rem : ExecWithin w (.op (.copy rRem rRem)) z1 z1 1 :=
            ⟨1, le_rfl, exec_nop rRem z1⟩
          have hinc : ∃ z2, ExecWithin w
              (ram[ rRem ← rRem + rOne ] : Code .standard 34) z1 z2 1 ∧
              ConstRegs g z2 ∧ z2.regs rChosen = chosen.val ∧ z2.regs rRem = k + 1 ∧
              z2.regs rCompLen = S.comp.length ∧ z2.regs rOuterIdx = x.regs rOuterIdx ∧
              z2.mem = z.mem := by
            wram_exec [hz1C.one, hz1Rem]
            exact ⟨by wram_simp [hz1C], by wram_simp [hz1Ch], by wram_simp, by wram_simp [hz1CL],
              by wram_simp [hz1Idx], by wram_simp [hz1m]⟩
          obtain ⟨z2, hz2_ex, hz2C, hz2Ch, hz2Rem, hz2CL, hz2Idx, hz2m⟩ := hinc
          have hsame_tab : tabAt (k + 1) = tabAt k := by
            rw [htab_next]
            have hgv' : (tabAt k).getD v none = none := hgv
            rw [hgv']
            simp only [freeze, Option.map_none]
            apply List.ext_getElem (by simp only [List.length_set])
            intro i hi1 hi2
            rw [List.getElem_set]
            split_ifs with hiv
            · subst hiv
              simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi2,
                Option.getD_some] using hgv'.symm
            · rfl
          refine ⟨z2, (hz1_ex.seq ((ExecWithin.branch_neg hc_br hnop_rem).seq hz2_ex)).mono
              (by omega),
            ⟨?_, hz2Ch, hz2CL, hz2Idx, hz2m ▸ hzCM⟩, hz2Rem⟩
          rw [hsame_tab]
          exact hzT.of_eq hz2C hz2m
        | some fn =>
          obtain ⟨hvis1, htab_fn⟩ := hzT.vis_some v hv_lt fn hgv
          have hc_br : (Cond.eq rTmp1 rOne).Holds z1 := by
            simp only [Cond.holds_eq, hz1T1, hvis1, hz1C.one]
          have : Fits w (v * L) := fits_top hw (by wram_omega)
          have : Fits w (tabBase g + v * L) := fits_top hw (by wram_omega)
          have : Fits w (tabBase g + v * L + chosen.val) :=
            fits_top hw (by have := chosen.isLt; wram_omega)
          have hprep_f : ∃ z2, ExecWithin w freezePrep z1 z2 5 ∧
              ConstRegs g z2 ∧ z2.regs rTmp2 = tabBase g + v * L ∧
              z2.regs rTmp3 = (fn chosen).val ∧ z2.regs rLabIdx = 0 ∧
              z2.regs rChosen = chosen.val ∧ z2.regs rRem = k ∧
              z2.regs rCompLen = S.comp.length ∧ z2.regs rOuterIdx = x.regs rOuterIdx ∧
              z2.mem = z.mem := by
            have hfc_mem : z1.mem (tabBase g + v * L + chosen.val) = (fn chosen).val := by
              rw [hz1m]; simpa only [Fin.eta] using htab_fn chosen.val chosen.isLt
            unfold freezePrep
            wram_exec [hz1C.zero, hz1C.regL, hz1C.tabB, hz1S, hz1Ch, hfc_mem]
            exact ⟨by wram_simp [hz1C], by wram_simp, by wram_simp, by wram_simp,
              by wram_simp [hz1Ch], by wram_simp [hz1Rem], by wram_simp [hz1CL],
              by wram_simp [hz1Idx], by wram_simp [hz1m]⟩
          obtain ⟨z2, hz2_ex, hz2C, hz2T2, hz2T3, hz2Lab, hz2Ch, hz2Rem, hz2CL, hz2Idx, hz2m⟩ :=
            hprep_f
          let Pslot (a : ℕ) (w0 : Data 34) : Prop :=
            ConstRegs g w0 ∧ w0.regs rTmp2 = tabBase g + v * L ∧
            w0.regs rTmp3 = (fn chosen).val ∧ w0.regs rChosen = chosen.val ∧
            w0.regs rRem = k ∧ w0.regs rCompLen = S.comp.length ∧
            w0.regs rOuterIdx = x.regs rOuterIdx ∧
            (∀ i < a, w0.mem (tabBase g + v * L + i) = (fn chosen).val) ∧
            ∀ addr, ¬ (tabBase g + v * L ≤ addr ∧ addr < tabBase g + v * L + a) →
              w0.mem addr = z.mem addr
          obtain ⟨z3, hz3_ex, ⟨hz3C, _, _, hz3Ch, hz3Rem, hz3CL, hz3Idx, hz3Row, hz3Fr⟩, _⟩ :=
            ExecWithin.loop_count (w := w) (index := rLabIdx) (limit := rL)
              (body := freezeSlotBody) (N := L) (T := 3) Pslot
              (fun w0 hw0 => hw0.1.regL)
              (fun w0 hw0 ha => by
                obtain ⟨hwC, hwT2, hwT3, hwCh, hwRem, hwCL, hwIdx, hwRow, hwFr⟩ := hw0
                set a := w0.regs rLabIdx
                have ha_reg : w0.regs rLabIdx = a := rfl
                have : Fits w (tabBase g + v * L + a) := fits_top hw (by wram_omega)
                have : Fits w (a + 1) := fits_top hw (by wram_omega)
                have hpws := prefix_write_step (e := fun _ => (fn chosen).val) hwRow hwFr
                  (rfl : Function.update w0.mem (tabBase g + v * L + a) (fn chosen).val = _)
                unfold freezeSlotBody
                wram_exec [hwC.one, hwT2, hwT3, ha_reg]
                refine ⟨⟨by wram_simp [hwC], by wram_simp [hwT2], by wram_simp [hwT3],
                  by wram_simp [hwCh], by wram_simp [hwRem], by wram_simp [hwCL],
                  by wram_simp [hwIdx], ?_, ?_⟩, by wram_simp⟩
                · simp only [Data.write_mem, Data.set_mem]; exact hpws.1
                · simp only [Data.write_mem, Data.set_mem]; exact hpws.2)
              (by rw [hz2Lab]; exact Nat.zero_le _)
              (by rw [hz2Lab]; exact ⟨hz2C, hz2T2, hz2T3, hz2Ch, hz2Rem, hz2CL, hz2Idx,
                fun _ h => by omega, fun addr _ => congrFun hz2m addr⟩)
          rw [hz2Lab, Nat.sub_zero] at hz3_ex
          have hinc : ∃ z4, ExecWithin w
              (ram[ rRem ← rRem + rOne ] : Code .standard 34) z3 z4 1 ∧
              ConstRegs g z4 ∧ z4.regs rChosen = chosen.val ∧ z4.regs rRem = k + 1 ∧
              z4.regs rCompLen = S.comp.length ∧ z4.regs rOuterIdx = x.regs rOuterIdx ∧
              z4.mem = z3.mem := by
            wram_exec [hz3C.one, hz3Rem]
            exact ⟨by wram_simp [hz3C], by wram_simp [hz3Ch], by wram_simp,
              by wram_simp [hz3CL], by wram_simp [hz3Idx], by wram_simp⟩
          obtain ⟨z4, hz4_ex, hz4C, hz4Ch, hz4Rem, hz4CL, hz4Idx, hz4m⟩ := hinc
          have hfr_low : ∀ a < tabBase g, z4.mem a = z.mem a := fun a ha => by
            rw [hz4m]; exact hz3Fr a (by omega)
          refine ⟨z4, (hz1_ex.seq ((ExecWithin.branch_pos hc_br (hz2_ex.seq hz3_ex)).seq
              hz4_ex)).mono (by omega),
            ⟨?_, hz4Ch, hz4CL, hz4Idx, hzCM.frame fun a ha1 _ => by
              rw [hz4m]; exact hz3Fr a (by wram_omega)⟩, hz4Rem⟩
          have hlen_k : (tabAt k).length = slots g := hzT.len_table
          have hgv' : (tabAt k).getD v none = some fn := hgv
          refine ⟨hz4C, hzT.inp.frame (fun a ha => hfr_low a (by wram_omega)),
            hzT.bkt.frame (fun a ha => hfr_low a (by wram_omega)),
            by rw [htab_next, List.length_set, hlen_k],
            fun u hu hun => ?_, fun u hu fn' huf => ?_⟩
          · rw [hfr_low _ (by wram_omega)]
            have huv : u ≠ v := by
              rintro rfl
              change (tabAt (k + 1)).getD v none = none at hun
              rw [htab_next, List.getD_set_self (hlen_k ▸ hv_lt), hgv'] at hun
              nomatch hun
            have hun' : ({ S with table := tabAt k } : State (Fin L)).get u = none := by
              change (tabAt (k + 1)).getD u none = none at hun
              rwa [htab_next, List.getD_set_ne (Ne.symm huv)] at hun
            exact hzT.vis_none u hu hun'
          · by_cases huv : u = v
            · subst huv
              change (tabAt (k + 1)).getD v none = some fn' at huf
              rw [htab_next, List.getD_set_self (hlen_k ▸ hv_lt), hgv'] at huf
              simp only [freeze, Option.map_some, Option.some.injEq] at huf
              subst huf
              exact ⟨by rw [hfr_low _ (by wram_omega)]; exact hvis1,
                fun a ha => by rw [hz4m]; exact hz3Row a ha⟩
            · have huf' : ({ S with table := tabAt k } : State (Fin L)).get u = some fn' := by
                change (tabAt (k + 1)).getD u none = some fn' at huf
                rwa [htab_next, List.getD_set_ne (Ne.symm huv)] at huf
              obtain ⟨hu1, hutab⟩ := hzT.vis_some u hu fn' huf'
              exact ⟨by rw [hfr_low _ (by wram_omega)]; exact hu1,
                fun a ha => by rw [hz4m, hz3Fr _ (not_in_tabRow huv ha)]; exact hutab a ha⟩)
      (by rw [hrem3]; exact Nat.zero_le _)
      (by rw [hrem3]; exact ⟨hT3, hch3, hcl3, hidx3, hcm3⟩)
  rw [hrem3, Nat.sub_zero] at hx4
  have hclr : ∃ y, ExecWithin w (ram[ rCompLen ← rZero ] : Code .standard 34) x4 y 1 ∧
      ConstRegs g y ∧ y.regs rOuterIdx = x.regs rOuterIdx ∧ y.mem = x4.mem := by
    wram_exec [hT4.consts.zero]
    exact ⟨by wram_simp [hT4.consts], by wram_simp [hidx4], by wram_simp⟩
  obtain ⟨y, hx5, hc5, hidx5, hm5⟩ := hclr
  have htab_end : tabAt S.comp.length = (settle (List.finRange L) S).table := by
    simp only [tabAt, settle, chosen, List.take_length]
  have hmul_frz : S.comp.length * (5 * L + 20 + 2) = freezePass L * S.comp.length := by
    simp only [freezePass]; ring
  refine ⟨y, (hx1.seq (hx2.seq (hx3.seq (hx4.seq hx5)))).mono (by omega),
    ⟨hc5, hm5 ▸ hT4.inp, hm5 ▸ hT4.bkt, ?_, fun v hv hvn => ?_, fun v hv fn hvf => ?_⟩, hidx5⟩
  · rw [← htab_end]; exact hT4.len_table
  · rw [hm5]; exact hT4.vis_none v hv (by simpa only [State.get, htab_end] using hvn)
  · rw [hm5]; exact hT4.vis_some v hv fn (by simpa only [State.get, htab_end] using hvf)

private theorem sum_length_adj_le_fin {L : ℕ} (g : Graph (Fin L → Fin L)) :
    ∑ v ∈ Finset.range (slots g), (adj g v).length ≤ 2 * g.edges.length := by
  have key : ∀ (l : List (Edge (Fin L → Fin L))) (s : Finset ℕ),
      ∑ v ∈ s, (l.filter (incident v)).length ≤ 2 * l.length := by
    intro l s
    induction l with
    | nil => simp only [List.filter_nil, List.length_nil, Finset.sum_const_zero, mul_zero, le_refl]
    | cons e l ih =>
      have hcount : ∀ v, ((e :: l).filter (incident v)).length =
          (l.filter (incident v)).length + if incident v e then 1 else 0 := by
        intro v
        rw [List.filter_cons]
        split_ifs <;> simp only [List.length_cons, Nat.add_zero]
      simp only [hcount, Finset.sum_add_distrib, List.length_cons]
      have h2 : ∑ v ∈ s, (if incident v e = true then 1 else 0) ≤ 2 := by
        rw [Finset.sum_boole]
        refine (Finset.card_le_card (t := {e.src, e.dst}) ?_).trans Finset.card_le_two
        intro v hv
        simp only [Finset.mem_filter, incident, Bool.or_eq_true, beq_iff_eq] at hv
        rcases hv.2 with h | h <;>
          simp only [h, Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
      omega
  exact key _ _

private theorem stepsLoop_spec {L w : ℕ} [NeZero L] (g : Graph (Fin L → Fin L)) (x : Data 34)
    (hT : TableStateAt g (init g) x) (hidx0 : x.regs rOuterIdx = 0)
    (hw : Fits w (wordBound g)) :
    ∃ y, ExecWithin w stepsLoop x y
        ((5 * L + 38) * slots g + (106 * L + 152) * g.edges.length + 2) ∧
      TableStateAt g (run (List.finRange L) g) y := by
  have hewb := edges_lt_wordBound g
  have hstep_one : ∀ (j : ℕ) (hj : j < g.edges.length) (S : State (Fin L)) (z : Data 34),
      TableStateAt g S z → z.regs rOuterIdx = j → S.comp = [] → S.stack = [] →
      ∃ y t, Exec w stepBody z y t ∧
        t + creditRAM g (step (List.finRange L) g S g.edges[j]) ≤
          creditRAM g S + (18 * L + 38) ∧
        TableStateAt g (step (List.finRange L) g S g.edges[j]) y ∧
        (step (List.finRange L) g S g.edges[j]).comp = [] ∧
        (step (List.finRange L) g S g.edges[j]).stack = [] ∧
        y.regs rOuterIdx = j + 1 := by
    intro j hj S z hzT hzIdx hzComp hzStk
    set e := g.edges[j]
    have hs_lt : e.src < slots g := src_lt_slots (List.getElem_mem hj)
    have hed := edge_end_le_wordBound hj
    have : Fits w (j * (L + 2)) := hw.of_le (by omega)
    have : Fits w (4 + j * (L + 2)) := hw.of_le (by omega)
    have : Fits w (visBase g + e.src) := fits_top hw (by wram_omega)
    have : Fits w (j + 1) := hw.of_le (by omega)
    have hhead : ∃ z1, ExecWithin w stepHead z z1 5 ∧
        TableStateAt g S z1 ∧ z1.regs rSrc = e.src ∧ z1.regs rTmp1 = z.mem (visBase g + e.src) ∧
        z1.regs rOuterIdx = j := by
      unfold stepHead
      wram_exec [hzT.consts.stride, hzT.consts.edgeB, hzT.consts.visB, hzIdx,
        hzT.inp.edge_src j hj]
      exact ⟨hzT.of_eq (by wram_simp [hzT.consts]) (by wram_simp),
        by wram_simp; rfl, by wram_simp; rfl, by wram_simp [hzIdx]⟩
    obtain ⟨z1, ⟨th, hth, hexh⟩, hz1T, hz1S, hz1T1, hz1Idx⟩ := hhead
    cases hgs : S.get e.src with
    | some fn =>
      obtain ⟨hvis1, _⟩ := hzT.vis_some e.src hs_lt fn hgs
      have hc_br : ¬ (Cond.eq rTmp1 rZero).Holds z1 := by
        simp only [Cond.holds_eq, hz1T1, hvis1, hz1T.consts.zero, Nat.one_ne_zero,
          not_false_eq_true]
      have hnop : Exec w (.op (.copy rOuterIdx rOuterIdx)) z1 z1 1 := exec_nop rOuterIdx z1
      have hinc : ∃ y,
          ExecWithin w (ram[ rOuterIdx ← rOuterIdx + rOne ] : Code .standard 34) z1 y 1 ∧
          TableStateAt g S y ∧ y.regs rOuterIdx = j + 1 := by
        wram_exec [hz1T.consts.one, hz1Idx]
        exact ⟨hz1T.of_eq (by wram_simp [hz1T.consts]) (by wram_simp), by wram_simp⟩
      obtain ⟨y, ⟨ti, hti, hexi⟩, hyT, hyIdx⟩ := hinc
      have hstep_eq : step (List.finRange L) g S e = S := by simp only [step, hgs]
      rw [hstep_eq]
      exact ⟨y, th + (1 + 2 + ti), hexh.seq ((Exec.branch_neg hc_br hnop).seq hexi),
        by omega, hyT, hzComp, hzStk, hyIdx⟩
    | none =>
      have hvis0 : z.mem (visBase g + e.src) = 0 := hzT.vis_none e.src hs_lt hgs
      have hc_br : (Cond.eq rTmp1 rZero).Holds z1 := by
        simp only [Cond.holds_eq, hz1T1, hvis0, hz1T.consts.zero]
      obtain ⟨z2, ⟨ts, hts, hexs⟩, hz2S, hz2Idx⟩ :=
        startCode_spec (w := w) g S z1 e.src hz1T hz1S hs_lt hgs hw
      obtain ⟨z3, te, hexe, hcred_e, hz3S, hz3Idx⟩ :=
        exploreCode_spec (w := w) g (start S e.src) z2 hz2S rfl hw
      obtain ⟨z4, ⟨tf, htf, hexf⟩, hz4T, hz4Idx⟩ :=
        settleCode_spec (w := w) g ((scan (List.finRange L) g)^[slots g] (start S e.src))
          z3 hz3S hw
      have hinc : ∃ y,
          ExecWithin w (ram[ rOuterIdx ← rOuterIdx + rOne ] : Code .standard 34) z4 y 1 ∧
          TableStateAt g (settle (List.finRange L)
            ((scan (List.finRange L) g)^[slots g] (start S e.src))) y ∧
          y.regs rOuterIdx = j + 1 := by
        wram_exec [hz4T.consts.one, hz4Idx.trans (hz3Idx.trans (hz2Idx.trans hz1Idx))]
        exact ⟨hz4T.of_eq (by wram_simp [hz4T.consts]) (by wram_simp), by wram_simp⟩
      obtain ⟨y, ⟨ti, hti, hexi⟩, hyT, hyIdx⟩ := hinc
      have hstep_eq : step (List.finRange L) g S e =
          settle (List.finRange L) ((scan (List.finRange L) g)^[slots g] (start S e.src)) := by
        simp only [step, hgs]
      rw [hstep_eq]
      have hstk_end : ((scan (List.finRange L) g)^[slots g] (start S e.src)).stack = [] :=
        iterate_scan_eq_nil (List.finRange L) g
          (by simp only [start, List.length_set, hzT.len_table])
          (potential_start hzT.len_table (hzT.len_table ▸ hs_lt))
      have hcred_start : creditRAM g (start S e.src) ≤ creditRAM g S := by
        have hun : (start S e.src).unvisited = S.unvisited.erase e.src :=
          unvisited_push (hzT.len_table ▸ hs_lt) id
        have hsum := Finset.sum_erase_add _ (weightRAM g)
          (mem_unvisited (hzT.len_table ▸ hs_lt) hgs)
        unfold creditRAM State.wpot
        rw [hun]
        simp only [start, hzComp, hzStk, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil, List.length_nil, mul_zero, add_zero]
        omega
      have hcred_settle : creditRAM g (settle (List.finRange L)
          ((scan (List.finRange L) g)^[slots g] (start S e.src))) =
          ((scan (List.finRange L) g)^[slots g] (start S e.src)).wpot (weightRAM g) := by
        set Tscan := (scan (List.finRange L) g)^[slots g] (start S e.src)
        unfold creditRAM State.wpot
        rw [unvisited_settle (List.finRange L) Tscan]
        simp only [settle, hstk_end, List.map_nil, List.sum_nil, List.length_nil, mul_zero,
          add_zero]
      have hcred_Tscan : creditRAM g ((scan (List.finRange L) g)^[slots g] (start S e.src)) =
          ((scan (List.finRange L) g)^[slots g] (start S e.src)).wpot (weightRAM g) +
            freezePass L *
              ((scan (List.finRange L) g)^[slots g] (start S e.src)).comp.length := rfl
      refine ⟨y, th + ((ts + (te + tf) + 1) + ti),
        hexh.seq ((Exec.branch_pos hc_br (hexs.seq (hexe.seq hexf))).seq hexi),
        by omega, hyT, rfl, hstk_end, hyIdx⟩
  suffices hrem_edges : ∀ (m : ℕ) (hm : m ≤ g.edges.length)
      (S : State (Fin L)) (z : Data 34),
      TableStateAt g S z → z.regs rOuterIdx = g.edges.length - m → S.comp = [] → S.stack = [] →
      ∃ y t, Exec w stepsLoop z y t ∧
        t + creditRAM g ((g.edges.drop (g.edges.length - m)).foldl (step (List.finRange L) g) S) ≤
          creditRAM g S + (18 * L + 40) * m + 2 ∧
        TableStateAt g ((g.edges.drop (g.edges.length - m)).foldl (step (List.finRange L) g) S) y by
    obtain ⟨y, t, hexl, hcred, hyT⟩ :=
      hrem_edges g.edges.length le_rfl (init g) x hT (by rw [hidx0, Nat.sub_self]) rfl rfl
    simp only [Nat.sub_self, List.drop_zero] at hcred hyT
    have hinit_cred : creditRAM g (init g) ≤
        (5 * L + 38) * slots g + (88 * L + 112) * g.edges.length := by
      have hun : (init g).unvisited = Finset.range (slots g) := by
        ext v
        simp only [State.unvisited, init, State.get, List.length_replicate, Finset.mem_filter,
          Finset.mem_range, and_iff_left_iff_imp]
        intro hv
        simp only [List.getD_replicate, hv, Option.isNone_none]
      unfold creditRAM State.wpot
      rw [hun]
      simp only [init, List.map_nil, List.sum_nil, List.length_nil,
        mul_zero, add_zero, weightRAM, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
        smul_eq_mul, ← Finset.mul_sum]
      have hadj := Nat.mul_le_mul_left (visitPass L) (sum_length_adj_le_fin g)
      simp only [visitPass] at hadj ⊢
      nlinarith
    exact ⟨y, ⟨t, by nlinarith, hexl⟩, hyT⟩
  intro m
  induction m with
  | zero =>
    intro _ S z hzT hzIdx _ _
    simp only [Nat.sub_zero, List.drop_length, List.foldl_nil] at hzIdx ⊢
    exact ⟨z, 2, .loop_exit (by simp only [Cond.holds_lt, hzIdx, hzT.consts.regE]; omega),
      by omega, hzT⟩
  | succ m ih =>
    intro hm S z hzT hzIdx hzComp hzStk
    set j := g.edges.length - (m + 1)
    have hj : j < g.edges.length := by omega
    have hc_loop : (Cond.lt rOuterIdx rE).Holds z := by
      simp only [Cond.holds_lt, hzIdx, hzT.consts.regE]; omega
    obtain ⟨z1, t1, hex1, hcred1, hz1T, hz1Comp, hz1Stk, hz1Idx⟩ :=
      hstep_one j hj S z hzT hzIdx hzComp hzStk
    have hidx1_eq : z1.regs rOuterIdx = g.edges.length - m := by omega
    obtain ⟨y, t2, hex2, hcred2, hyT⟩ :=
      ih (by omega) (step (List.finRange L) g S g.edges[j]) z1 hz1T hidx1_eq hz1Comp hz1Stk
    have hdrop : g.edges.drop j = g.edges[j] :: g.edges.drop (g.edges.length - m) := by
      rw [show g.edges.length - m = j + 1 by omega]
      exact List.drop_eq_getElem_cons hj
    rw [hdrop, List.foldl_cons]
    exact ⟨y, t1 + t2 + 2, .loop_iter hc_loop hex1 hex2,
      by simp only [Nat.mul_succ]; omega, hyT⟩

/-! ## Phase 4: Extraction, edge checking, output array header, and public theorems -/

private theorem extractCode_spec {L w : ℕ} [NeZero L] (g : Graph (Fin L → Fin L)) (x : Data 34)
    (hT : TableStateAt g (run (List.finRange L) g) x) (hw : Fits w (wordBound g)) :
    ∃ y, ExecWithin w extractCode x y (slots g * 12 + 3) ∧
      ConstRegs g y ∧ InputAt g y.mem ∧
      HoldsList (outBaseAddr g + 2)
        ((List.range (slots g)).map fun v => (labelling (List.finRange L) g v).val) y.mem := by
  have hset0 : ∃ x0, ExecWithin w (ram[ rOuterIdx ← rZero ] : Code .standard 34) x x0 1 ∧
      TableStateAt g (run (List.finRange L) g) x0 ∧ x0.regs rOuterIdx = 0 := by
    wram_exec [hT.consts.zero]
    exact ⟨hT.of_eq (by wram_simp [hT.consts]) (by wram_simp), by wram_simp⟩
  obtain ⟨x0, hx0, hT0, hidx0⟩ := hset0
  let labVal (v : ℕ) : ℕ := (labelling (List.finRange L) g v).val
  let P (k : ℕ) (z : Data 34) : Prop :=
    ConstRegs g z ∧
    (∀ v < k, z.mem (outBaseAddr g + 2 + v) = labVal v) ∧
    ∀ addr, ¬ (outBaseAddr g + 2 ≤ addr ∧ addr < outBaseAddr g + 2 + k) → z.mem addr = x0.mem addr
  obtain ⟨y, hy, ⟨hyC, hyOut, hyFr⟩, _⟩ :=
    ExecWithin.loop_count (w := w) (index := rOuterIdx) (limit := rN) (body := extractBody)
      (N := slots g) (T := 10) P
      (fun z hz => hz.1.regN)
      (fun z hz hv => by
        obtain ⟨hzC, hzOut, hzFr⟩ := hz
        set v := z.regs rOuterIdx
        have hv_reg : z.regs rOuterIdx = v := rfl
        have : Fits w (visBase g + v) := fits_top hw (by wram_omega)
        have : Fits w (outBaseAddr g + 2) := fits_top hw (by wram_omega)
        have : Fits w (outBaseAddr g + 2 + v) := fits_top hw (by wram_omega)
        have : Fits w (v + 1) := fits_top hw (by wram_omega)
        cases hgv : (run (List.finRange L) g).get v with
        | none =>
          have hvis0 : z.mem (visBase g + v) = 0 := by
            rw [hzFr _ (by wram_omega)]
            exact hT0.vis_none v hv hgv
          have hlv0 : labVal v = 0 := by
            simp only [labVal, labelling, hgv, Option.elim_none, default, Fin.val_zero]
          have hpws := prefix_write_step hzOut hzFr
            (show Function.update z.mem (outBaseAddr g + 2 + v) 0 =
              Function.update z.mem (outBaseAddr g + 2 + v) (labVal v) by rw [hlv0])
          unfold extractBody
          wram_exec [hzC.zero, hzC.one, hzC.two, hzC.visB, hzC.outB, hv_reg, hvis0]
          refine ⟨⟨by wram_simp [hzC], ?_, ?_⟩, by wram_simp⟩
          · simp only [Data.write_mem, Data.set_mem]; exact hpws.1
          · simp only [Data.write_mem, Data.set_mem]; exact hpws.2
        | some fn =>
          obtain ⟨hvis1, htab_fn⟩ := hT0.vis_some v hv fn hgv
          have hvis1' : z.mem (visBase g + v) = 1 := by
            rw [hzFr _ (by wram_omega)]; exact hvis1
          have hv_cb := tabRow_hi_le_candBase (g := g) hv
          have hf0_mem : z.mem (tabBase g + v * L) = (fn default).val := by
            rw [hzFr _ (by wram_omega)]
            have h0_def : (⟨0, NeZero.pos L⟩ : Fin L) = default := rfl
            simpa only [Nat.add_zero, h0_def] using htab_fn 0 (NeZero.pos L)
          have hlv_fn : labVal v = (fn default).val := by
            simp only [labVal, labelling, hgv, Option.elim_some]
          have : Fits w (v * L) := fits_top hw (by wram_omega)
          have : Fits w (tabBase g + v * L) := fits_top hw (by wram_omega)
          have hpws := prefix_write_step hzOut hzFr
            (show Function.update z.mem (outBaseAddr g + 2 + v) (fn default).val =
              Function.update z.mem (outBaseAddr g + 2 + v) (labVal v) by rw [hlv_fn])
          unfold extractBody
          wram_exec [hzC.one, hzC.two, hzC.regL, hzC.visB, hzC.tabB, hzC.outB, hv_reg, hvis1',
            hf0_mem]
          refine ⟨⟨by wram_simp [hzC], ?_, ?_⟩, by wram_simp⟩
          · simp only [Data.write_mem, Data.set_mem]; exact hpws.1
          · simp only [Data.write_mem, Data.set_mem]; exact hpws.2)
      (by rw [hidx0]; exact Nat.zero_le _)
      (by rw [hidx0]; exact ⟨hT0.consts, fun _ h => by omega, fun _ _ => rfl⟩)
  rw [hidx0, Nat.sub_zero] at hy
  refine ⟨y, (hx0.seq hy).mono (by omega), hyC,
    hT0.inp.frame (fun a ha => hyFr a (by wram_omega)), fun i => ?_⟩
  have hi : i.val < slots g := by
    simpa only [List.length_map, List.length_range] using i.isLt
  change y.mem (outBaseAddr g + 2 + i.val) = _
  rw [hyOut i.val hi]
  simp only [labVal, Fin.getElem_fin, List.getElem_map, List.getElem_range]

private theorem checkCode_spec {L w : ℕ} [NeZero L] (g : Graph (Fin L → Fin L)) (x : Data 34)
    (hc : ConstRegs g x) (hinp : InputAt g x.mem)
    (hout : HoldsList (outBaseAddr g + 2)
      ((List.range (slots g)).map fun v => (labelling (List.finRange L) g v).val) x.mem)
    (hw : Fits w (wordBound g)) :
    ∃ y, ExecWithin w checkCode x y (g.edges.length * 19 + 4) ∧
      ConstRegs g y ∧
      y.regs ok = (check g (labelling (List.finRange L) g)).toNat ∧
      y.mem = x.mem := by
  have hewb := edges_lt_wordBound g
  have hset : ∃ x0, ExecWithin w checkInit x x0 2 ∧
      ConstRegs g x0 ∧ x0.regs ok = 1 ∧ x0.regs rOuterIdx = 0 ∧ x0.mem = x.mem := by
    unfold checkInit
    wram_exec [hc.zero, hc.one]
    exact ⟨by wram_simp [hc], by wram_simp, by wram_simp, by wram_simp⟩
  obtain ⟨x0, hx0, hc0, hok0, hidx0, hm0⟩ := hset
  set σ := labelling (List.finRange L) g
  let P (k : ℕ) (z : Data 34) : Prop :=
    ConstRegs g z ∧
    z.regs ok = ((g.edges.take k).all fun e => decide (e.constraint (σ e.src) = σ e.dst)).toNat ∧
    z.mem = x.mem
  obtain ⟨y, hy, ⟨hyC, hyOk, hyMem⟩, _⟩ :=
    ExecWithin.loop_count (w := w) (index := rOuterIdx) (limit := rE) (body := checkBody)
      (N := g.edges.length) (T := 17) P
      (fun z hz => hz.1.regE)
      (fun z hz hj => by
        obtain ⟨hzC, hzOk, hzMem⟩ := hz
        set j := z.regs rOuterIdx
        have hj_reg : z.regs rOuterIdx = j := rfl
        set e := g.edges[j]
        have hs_lt : e.src < slots g := src_lt_slots (List.getElem_mem hj)
        have hd_lt : e.dst < slots g := dst_lt_slots (List.getElem_mem hj)
        have hed := edge_end_le_wordBound hj
        have hsrc_ltL := (σ e.src).isLt
        have hsrc_mem : z.mem (4 + j * (L + 2)) = e.src := by
          rw [hzMem]; exact hinp.edge_src j hj
        have hdst_mem : z.mem (4 + j * (L + 2) + 1) = e.dst := by
          rw [hzMem]; exact hinp.edge_dst j hj
        have hlv : z.mem (outBaseAddr g + 2 + e.src) = (σ e.src).val := by
          rw [hzMem, hout.get e.src
            (by simp only [List.length_map, List.length_range]; exact hs_lt)]
          simp only [List.getElem_map, List.getElem_range]
        have hlw : z.mem (outBaseAddr g + 2 + e.dst) = (σ e.dst).val := by
          rw [hzMem, hout.get e.dst
            (by simp only [List.length_map, List.length_range]; exact hd_lt)]
          simp only [List.getElem_map, List.getElem_range]
        have hc_mem : z.mem (4 + j * (L + 2) + ((σ e.src).val + 2)) =
            (e.constraint (σ e.src)).val := by
          rw [hzMem, show 4 + j * (L + 2) + ((σ e.src).val + 2) =
            4 + j * (L + 2) + 2 + (σ e.src).val by omega]
          simpa only [Fin.eta] using hinp.edge_val j hj (σ e.src).val hsrc_ltL
        have : Fits w (j * (L + 2)) := hw.of_le (by omega)
        have : Fits w (4 + j * (L + 2)) := hw.of_le (by omega)
        have : Fits w (4 + j * (L + 2) + 1) := hw.of_le (by omega)
        have : Fits w (outBaseAddr g + 2) := fits_top hw (by wram_omega)
        have : Fits w (outBaseAddr g + 2 + e.src) := fits_top hw (by wram_omega)
        have : Fits w (outBaseAddr g + 2 + e.dst) := fits_top hw (by wram_omega)
        have : Fits w ((σ e.src).val + 2) := hw.of_le (by omega)
        have : Fits w (4 + j * (L + 2) + ((σ e.src).val + 2)) := hw.of_le (by omega)
        have : Fits w (j + 1) := hw.of_le (by omega)
        have hall_next : ((g.edges.take (j + 1)).all fun d =>
              decide (d.constraint (σ d.src) = σ d.dst)) =
            (((g.edges.take j).all fun d => decide (d.constraint (σ d.src) = σ d.dst)) &&
              decide (e.constraint (σ e.src) = σ e.dst)) := by
          rw [List.take_succ_eq_append_getElem hj, List.all_append, List.all_cons, List.all_nil,
            Bool.and_true]
        by_cases heq_v : (e.constraint (σ e.src)).val = (σ e.dst).val
        · have heq_f : e.constraint (σ e.src) = σ e.dst := Fin.ext heq_v
          unfold checkBody
          wram_exec [hzC.one, hzC.two, hzC.stride, hzC.edgeB, hzC.outB, hj_reg,
            hsrc_mem, hdst_mem, hlv, hlw, hc_mem, heq_v]
          refine ⟨⟨by wram_simp [hzC], ?_, by wram_simp [hzMem]⟩, by wram_simp⟩
          wram_simp [hzOk]
          rw [hall_next, decide_eq_true heq_f, Bool.and_true]
        · have hne_f : e.constraint (σ e.src) ≠ σ e.dst :=
            fun heq => heq_v (congrArg Fin.val heq)
          unfold checkBody
          wram_exec [hzC.zero, hzC.one, hzC.two, hzC.stride, hzC.edgeB, hzC.outB, hj_reg,
            hsrc_mem, hdst_mem, hlv, hlw, hc_mem, heq_v]
          refine ⟨⟨by wram_simp [hzC], ?_, by wram_simp [hzMem]⟩, by wram_simp⟩
          wram_simp
          rw [hall_next, decide_eq_false hne_f, Bool.and_false, Bool.toNat_false])
      (by rw [hidx0]; exact Nat.zero_le _)
      (by rw [hidx0]
          exact ⟨hc0, by simp only [hok0, List.take_zero, List.all_nil, Bool.toNat_true], hm0⟩)
  rw [hidx0, Nat.sub_zero] at hy
  exact ⟨y, (hx0.seq hy).mono (by omega), hyC,
    by simpa only [check, List.take_length] using hyOk, hyMem⟩

private theorem finishCode_spec {L w : ℕ} [NeZero L] (g : Graph (Fin L → Fin L)) (x : Data 34)
    (hc : ConstRegs g x)
    (hok : x.regs ok = (check g (labelling (List.finRange L) g)).toNat)
    (hout : HoldsList (outBaseAddr g + 2)
      ((List.range (slots g)).map fun v => (labelling (List.finRange L) g v).val) x.mem)
    (hw : Fits w (wordBound g)) :
    ∃ y, ExecWithin w finishCode x y 6 ∧
      y.regs outBase = outBaseAddr g ∧
      y.regs ok = (solve (List.finRange L) g).isSome.toNat ∧
      outputList y.mem (y.regs outBase) =
        encodeSolution (slots g) (solve (List.finRange L) g) ∧
      Fits w (y.regs outBase + (encodeSolution (slots g) (solve (List.finRange L) g)).length) := by
  have : Fits w (outBaseAddr g + 1) := fits_top hw (by wram_omega)
  have : Fits w (slots g + 1) := fits_top hw (by wram_omega)
  cases hchk : check g (labelling (List.finRange L) g) with
  | true =>
    have hok1 : x.regs ok = 1 := by simp only [hok, hchk, Bool.toNat_true]
    have hsolve : solve (List.finRange L) g = some (labelling (List.finRange L) g) := by
      simp only [solve, hchk, ↓reduceIte]
    unfold finishCode
    wram_exec [hc.one, hc.regN, hc.outB, hok1]
    refine ⟨by wram_simp [hc.outB], by wram_simp [hok1]; rw [hsolve]; rfl, ?_, ?_⟩
    · wram_simp [hc.outB]
      rw [hsolve, outputList_eq_iff]
      refine ⟨by
          rw [Function.update_of_ne (by omega), Function.update_self]
          simp only [encodeSolution, List.length_cons, List.length_map, List.length_range], ?_⟩
      simp only [encodeSolution]
      refine holdsList_cons_iff.mpr
        ⟨by simp only [Function.update_self], hout.frame fun a ha1 _ => ?_⟩
      simp only [Function.update_of_ne (by omega : a ≠ outBaseAddr g + 1),
        Function.update_of_ne (by omega : a ≠ outBaseAddr g)]
    · wram_simp [hc.outB]; rw [hsolve]
      exact fits_top hw (by
        simp only [encodeSolution, List.length_cons, List.length_map, List.length_range]
        wram_omega)
  | false =>
    have hok0 : x.regs ok = 0 := by simp only [hok, hchk, Bool.toNat_false]
    have hsolve : solve (List.finRange L) g = none := by
      simp only [solve, hchk, Bool.false_eq_true, ↓reduceIte]
    unfold finishCode
    wram_exec [hc.zero, hc.one, hc.outB, hok0]
    refine ⟨by wram_simp [hc.outB], by wram_simp [hok0]; rw [hsolve]; rfl, ?_, ?_⟩
    · wram_simp [hc.outB]
      rw [hsolve, outputList_eq_iff]
      refine ⟨by
          rw [Function.update_of_ne (by omega), Function.update_self]
          simp only [encodeSolution, List.length_singleton], ?_⟩
      simp only [encodeSolution]
      exact holdsList_cons_iff.mpr ⟨by simp only [Function.update_self], holdsList_nil _ _⟩
    · wram_simp [hc.outB]; rw [hsolve]
      exact fits_top hw (by simp only [encodeSolution, List.length_singleton]; wram_omega)

/-- **Structured Word-RAM specification for `solveCode`:** from `Data.init (encode g)` at any
width `w` fitting `wordBound g`, `solveCode` terminates in at most `timeBound g - 1` steps with
`Reg.ok` equal to `(solve (List.finRange L) g).isSome.toNat` and `outputList` at `Reg.outBase`
equal to `encodeSolution (slots g) (solve (List.finRange L) g)` (whose end address fits in `w`). -/
theorem solveCode_spec {L w : ℕ} [NeZero L] (g : Graph (Fin L → Fin L))
    (hw : Fits w (wordBound g)) :
    ∃ y, ExecWithin w solveCode (Data.init (encode g)) y (timeBound g - 1) ∧
      y.regs ok = (solve (List.finRange L) g).isSome.toNat ∧
      outputList y.mem (y.regs outBase) =
        encodeSolution (slots g) (solve (List.finRange L) g) ∧
      Fits w (y.regs outBase + (encodeSolution (slots g) (solve (List.finRange L) g)).length) := by
  obtain ⟨x1, hx1, hc1, hinp1, hnf1, hidx1, hzero1⟩ := slotsSetup_spec (w := w) g hw
  obtain ⟨x2, hx2, hc2, hinp2, hbkt2, hzero2⟩ :=
    bucketsLoop_spec (w := w) g hc1 hinp1 hnf1 hidx1 hzero1 hw
  have hclr : ∃ x3, ExecWithin w resetStateCode x2 x3 3 ∧
      TableStateAt g (init g) x3 ∧ x3.regs rOuterIdx = 0 := by
    unfold resetStateCode
    wram_exec [hc2.zero]
    refine ⟨?_, by wram_simp⟩
    exact ⟨by wram_simp [hc2],
      by simp only [Data.set_mem]; exact hinp2,
      by simp only [Data.set_mem]; exact hbkt2,
      List.length_replicate,
      fun v _ _ => by
        simp only [Data.set_mem]
        exact hzero2 (visBase g + v) (Nat.le_add_right _ _),
      fun v hv fn hvf => by
        change ((init g).table.getD v none) = some fn at hvf
        simp only [init] at hvf
        rw [List.getD_replicate _ hv] at hvf
        nomatch hvf⟩
  obtain ⟨x3, hx3, hT3, hidx3⟩ := hclr
  obtain ⟨x4, hx4, hT4⟩ := stepsLoop_spec (w := w) g x3 hT3 hidx3 hw
  obtain ⟨x5, hx5, hc5, hinp5, hout5⟩ := extractCode_spec (w := w) g x4 hT4 hw
  obtain ⟨x6, hx6, hc6, hok6, hm6⟩ := checkCode_spec (w := w) g x5 hc5 hinp5 hout5 hw
  obtain ⟨y, hx7, _, hokY, houtList, hfitOut⟩ :=
    finishCode_spec (w := w) g x6 hc6 hok6 (hm6 ▸ hout5) hw
  have htot_le :
      16 * g.edges.length + 30 +
        (g.edges.length * 28 + 2 +
          (3 +
            ((5 * L + 38) * slots g + (106 * L + 152) * g.edges.length + 2 +
              (slots g * 12 + 3 + (g.edges.length * 19 + 4 + 6))))) ≤
        timeBound g - 1 := by
    rw [show timeBound g - 1 =
      (16 * L + 80) * slots g + (120 * L + 300) * g.edges.length + 79 by
      simp only [timeBound]; omega]
    nlinarith
  have htot : ExecWithin w solveCode (Data.init (encode g)) y (timeBound g - 1) :=
    (hx1.seq (hx2.seq (hx3.seq (hx4.seq (hx5.seq (hx6.seq hx7)))))).mono htot_le
  exact ⟨y, htot, hokY, houtList, hfitOut⟩

end Verification

/-- **Word-RAM label propagation (`ExecutesList`).** On any instance `g : Graph (Fin L → Fin L)`
(`[NeZero L]`) and any word width `w` fitting `wordBound g`, `program` halts in at most
`timeBound g` (`O(L · (slots g + |g.edges|))`) instructions and outputs
`encodeSolution (slots g) (solve (List.finRange L) g)`. -/
theorem program_spec {L w : ℕ} [NeZero L] (g : Graph (Fin L → Fin L))
    (hw : Fits w (wordBound g)) :
    ∃ n ≤ timeBound g,
      ExecutesList w program (.init (encode g))
        (encodeSolution (slots g) (solve (List.finRange L) g)) n := by
  obtain ⟨y, ⟨m, hm, he⟩, _, hout, hfit⟩ := solveCode_spec (w := w) g hw
  have hpos : 1 ≤ timeBound g := by simp only [timeBound]; omega
  exact ⟨m + 1, by omega, hout ▸ he.executesList outBase (by rwa [hout])⟩

/-- **Word-RAM label propagation on well-formed instances (`slots g = g.vertices`).** -/
theorem program_spec_of_wellFormed {L w : ℕ} [NeZero L] {g : Graph (Fin L → Fin L)}
    (hg : g.WellFormed) (hw : Fits w (wordBound g)) :
    ∃ n ≤ (16 * L + 80) * g.vertices + (120 * L + 300) * g.edges.length + 80,
      ExecutesList w program (.init (encode g))
        (encodeSolution g.vertices (solve (List.finRange L) g)) n := by
  obtain ⟨n, hn, hex⟩ := program_spec (w := w) g hw
  rw [timeBound, slots_eq_vertices hg] at hn
  rw [slots_eq_vertices hg] at hex
  exact ⟨n, hn, hex⟩

/-- `program` uniformly computes `encodeSolution (slots g) (solve (List.finRange L) g)` in
`timeBound g` instructions at every width `w` fitting `wordBound g`. -/
theorem computesListInTime_program (L : ℕ) [NeZero L] :
    program.ComputesListInTime (fun _ (g : Graph (Fin L → Fin L)) => encode g)
      (fun g _ => timeBound g) (fun g w => Fits w (wordBound g))
      (fun g => encodeSolution (slots g) (solve (List.finRange L) g)) := by
  intro g w hw _
  obtain ⟨n, hn, hex⟩ := program_spec (w := w) g hw
  exact ⟨n, hex, hn⟩

/-- **Word-RAM label propagation decision certificate (`Executes`).** On any instance
`g : Graph (Fin L → Fin L)` (`[NeZero L]`) and any word width `w` fitting `wordBound g`,
`decideProgram` halts in at most `timeBound g` instructions and outputs
`(solve (List.finRange L) g).isSome.toNat`. -/
theorem decideProgram_spec {L w : ℕ} [NeZero L] (g : Graph (Fin L → Fin L))
    (hw : Fits w (wordBound g)) :
    ∃ n ≤ timeBound g,
      Executes w decideProgram (.init (encode g))
        (solve (List.finRange L) g).isSome.toNat n := by
  obtain ⟨y, ⟨m, hm, he⟩, hok, _, _⟩ := solveCode_spec (w := w) g hw
  have hpos : 1 ≤ timeBound g := by simp only [timeBound]; omega
  exact ⟨m + 1, by omega, hok ▸ he.executes ok⟩

/-- `decideProgram` uniformly computes `(solve (List.finRange L) g).isSome.toNat` in `timeBound g`
instructions at every width `w` fitting `wordBound g`. -/
theorem computesInTime_decideProgram (L : ℕ) [NeZero L] :
    decideProgram.ComputesInTime (fun _ (g : Graph (Fin L → Fin L)) => encode g)
      (fun g _ => timeBound g) (fun g w => Fits w (wordBound g))
      (fun g => (solve (List.finRange L) g).isSome.toNat) := by
  intro g w hw _
  obtain ⟨n, hn, hex⟩ := decideProgram_spec (w := w) g hw
  exact ⟨n, hex, hn⟩

end Cslib.Complexity.UniqueGames.Propagation
