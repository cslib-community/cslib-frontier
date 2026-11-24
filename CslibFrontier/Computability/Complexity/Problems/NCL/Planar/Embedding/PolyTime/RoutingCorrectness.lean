/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.Embedding.PolyTime.Routing
public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.Embedding.PolyTime.Serialization
import all CslibFrontier.Computability.Complexity.Problems.NCL.Planar.Embedding.PolyTime.Routing
import all CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Permutation
import Mathlib.Data.List.Zip
import Mathlib.Tactic.FinCases

/-!
# Exact adjacent-swap routing order

Prefix filtering emits the same leftward crossings as the canonical incidence permutation.
The comparison retains the primitive word's offsets and order of wire creation.

## References

* [R. A. Hearn and E. D. Demaine, *PSPACE-completeness of sliding-block puzzles and other
  problems through the nondeterministic constraint logic model of computation*][HearnDemaine2005]
-/

public section

namespace Cslib.Complexity.NCL.Planar.Embedding.PolyTime

open Diagram

private theorem remaining_zero (ys xs : List Wire) : remaining ys xs 0 = xs := by
  simp [remaining]

private theorem remaining_cons (ys xs : List Wire) (hx : xs.Nodup) (y : Wire) (i : ℕ) :
    remaining (y :: ys) xs (i + 1) = remaining ys (xs.erase y) i := by
  simp only [remaining, List.take_succ_cons, hx.erase_eq_filter, List.filter_filter]
  apply List.filter_congr
  intro w _hw
  by_cases he : w = y
  · subst w
    simp
  · simp [he]

private theorem program_cons (ys xs : List Wire) (hx : xs.Nodup) (y : Wire) (k : ℕ) :
    RoutingData.program ⟨y :: ys, xs, k⟩ = pull k y (before y xs) ++
      RoutingData.program ⟨ys, xs.erase y, k + 1⟩ := by
  simp only [RoutingData.program, List.zipIdx_cons', List.flatMap_cons, List.flatMap_map,
    Nat.add_zero, remaining_zero]
  congr 1
  apply List.flatMap_congr
  rintro ⟨w, i⟩ _hp
  change pull (k + (i + 1)) w (before w (remaining (y :: ys) xs (i + 1))) = _
  rw [remaining_cons ys xs hx y i]
  congr 1
  omega

private theorem pull_cons (k : ℕ) (y x : Wire) (xs : List Wire) :
    pull k y (x :: xs) = pull (k + 1) y xs ++
      [(k, Opcode.cross x.color y.color x.bit y.bit)] := by
  simp only [pull, List.zipIdx_cons', List.reverse_cons, ← List.map_reverse,
    List.map_append, List.map_cons, List.map_nil, List.map_map, Nat.add_zero]
  congr 1
  apply List.map_congr_left
  rintro ⟨w, i⟩ _hp
  change (k + (i + 1), _) = (k + 1 + i, _)
  congr 1
  omega

private theorem expand_pull {Label : Type} (wire : Label → Wire) (xs : List Label)
    (y : Label) (post : List Color) (k : ℕ) :
    expand (pull k (wire y) (xs.map wire)) =
      (planarizeAlong Cell.expand
        (Diagram.moveLeft (Γ := Cell) (xs.map (fun x => (wire x).color))
          (wire y).color post)).toWord Prim.interp k := by
  induction xs generalizing k with
  | nil => rfl
  | cons x xs ih =>
    rw [List.map_cons, pull_cons]
    rw [expand_append, expand_cross]
    rw [ih]
    change _ =
      (((Diagram.id [(wire x).color]).tensor
        (planarizeAlong Cell.expand
          (Diagram.moveLeft (Γ := Cell) (xs.map (fun z => (wire z).color))
            (wire y).color post))).comp
        ((Crossover.diagram (wire x).color (wire y).color).tensor
          (Diagram.id (xs.map (fun z => (wire z).color) ++ post)))).toWord Prim.interp k
    simp only [toWord, List.nil_append, List.append_nil, List.length_cons, List.length_nil]

private theorem before_append {Label : Type} (wire : Label → Wire)
    (hi : Function.Injective wire) (pre post : List Label) (y : Label) (hy : y ∉ pre) :
    before (wire y) ((pre ++ y :: post).map wire) = pre.map wire := by
  have hm : wire y ∉ pre.map wire := by simpa only [List.mem_map, hi.eq_iff, exists_eq_right]
  simp only [before, List.map_append, List.map_cons]
  rw [List.idxOf_append_of_notMem hm]
  simp only [List.idxOf_cons_self, Nat.add_zero, List.take_left]

private theorem split_nodup {Label : Type} {pre post : List Label} {y : Label}
    (hn : (pre ++ y :: post).Nodup) : y ∉ pre ∧ (pre ++ post).Nodup := by
  have hnd := List.nodup_cons.mp (List.perm_middle.nodup_iff.mp hn)
  exact ⟨fun h => hnd.1 (List.mem_append_left post h), hnd.2⟩

private theorem program_split {Label : Type} (wire : Label → Wire)
    (hi : Function.Injective wire) (ys pre post : List Label) (y : Label)
    (hn : (pre ++ y :: post).Nodup) (k : ℕ) :
    RoutingData.program ⟨(y :: ys).map wire, (pre ++ y :: post).map wire, k⟩ =
      pull k (wire y) (pre.map wire) ++
        RoutingData.program ⟨ys.map wire, (pre ++ post).map wire, k + 1⟩ := by
  classical
  have hy := (split_nodup hn).1
  rw [List.map_cons, program_cons _ _ (hn.map hi)]
  rw [before_append wire hi pre post y hy, ← List.map_erase hi,
    List.erase_append_right (y :: post) hy, List.erase_cons_head]

private def boundedWord {Label : Type} {a b : List Color} {xs ys : List Label}
    (W : BoundedWiring (Γ := Cell) a b xs ys) (k : ℕ) : Word :=
  (planarizeAlong Cell.expand W.wiring.diagram).toWord Prim.interp k

private theorem boundedWord_transport {Label : Type} {a b a' b' : List Color}
    {xs ys xs' ys' : List Label} (ha : a = a') (hb : b = b') (hx : xs = xs') (hy : ys = ys')
    (h : BoundedWiring (Γ := Cell) a b xs ys = BoundedWiring (Γ := Cell) a' b' xs' ys')
    (W : BoundedWiring (Γ := Cell) a b xs ys) (k : ℕ) :
    boundedWord (h.mp W) k = boundedWord W k := by
  subst a' b' xs' ys'
  rfl

private theorem boundedWord_transport_rev {Label : Type} {a b a' b' : List Color}
    {xs ys xs' ys' : List Label} (ha : a = a') (hb : b = b') (hx : xs = xs') (hy : ys = ys')
    (h : BoundedWiring (Γ := Cell) a' b' xs' ys' = BoundedWiring (Γ := Cell) a b xs ys)
    (W : BoundedWiring (Γ := Cell) a b xs ys) (k : ℕ) :
    boundedWord (h.mpr W) k = boundedWord W k := by
  subst a' b' xs' ys'
  rfl

private theorem labelledBits_swap {Label : Type} (c d : Color) (x y : Label)
    (u : Label → Bool) :
    labelledBits (Labeling.swap (Γ := Cell) c d x y) u =
      (Opcode.cross c d (u x) (u y)).configuration := by
  have h : u ∘ (Labeling.swap (Γ := Cell) c d x y).label =
      Sum.elim (fun i : Fin 2 => ![u x, u y] i) Empty.elim := by
    funext i
    rcases i with i | i
    · fin_cases i <;> rfl
    · exact i.elim
  exact (congrArg (extendedBits (swap c d)) h).trans
    (extendedBits_swap c d ![u x, u y])

private theorem bits_pull {Label : Type} (wire : Label → Wire) (pre post : List Label)
    (y : Label) (k : ℕ) :
    configurationBits (pull k (wire y) (pre.map wire)) =
      labelledBits (Labeling.moveLeft (Γ := Cell) (wire y).color y
        (post.map (fun a => (wire a).color)) post (List.length_map ..).symm
        (pre.map (fun a => (wire a).color)) pre (List.length_map ..).symm)
        (fun a => (wire a).bit) := by
  induction pre generalizing k with
  | nil => rfl
  | cons x xs ih =>
    rw [List.map_cons, pull_cons]
    rw [configurationBits_append, configurationBits_singleton]
    rw [ih]
    change _ = labelledBits
      (((Labeling.id [(wire x).color] [x] rfl).tensor
        (Labeling.moveLeft (Γ := Cell) (wire y).color y
          (post.map (fun a => (wire a).color)) post (List.length_map ..).symm
          (xs.map (fun a => (wire a).color)) xs (List.length_map ..).symm)).comp
        ((Labeling.swap (wire x).color (wire y).color x y).tensor
          (Labeling.id (xs.map (fun a => (wire a).color) ++ post.map (fun a => (wire a).color))
            (xs ++ post) (by simp)))) (fun a => (wire a).bit)
    simp only [labelledBits_comp, labelledBits_tensor, labelledBits_id, labelledBits_swap,
      List.nil_append]
    change _ = _ ++
      ((Opcode.cross (wire x).color (wire y).color (wire x).bit (wire y).bit).configuration ++ [])
    rw [List.append_nil]

private def boundedBits {Label : Type} {a b : List Color} {xs ys : List Label}
    (W : BoundedWiring (Γ := Cell) a b xs ys) (u : Label → Bool) : List Bool :=
  labelledBits W.wiring.labeling u

private theorem boundedBits_transport {Label : Type} {a b a' b' : List Color}
    {xs ys xs' ys' : List Label} (ha : a = a') (hb : b = b') (hx : xs = xs') (hy : ys = ys')
    (h : BoundedWiring (Γ := Cell) a b xs ys = BoundedWiring (Γ := Cell) a' b' xs' ys')
    (W : BoundedWiring (Γ := Cell) a b xs ys) (u : Label → Bool) :
    boundedBits (h.mp W) u = boundedBits W u := by
  subst a' b' xs' ys'
  rfl

private theorem boundedBits_transport_rev {Label : Type} {a b a' b' : List Color}
    {xs ys xs' ys' : List Label} (ha : a = a') (hb : b = b') (hx : xs = xs') (hy : ys = ys')
    (h : BoundedWiring (Γ := Cell) a' b' xs' ys' = BoundedWiring (Γ := Cell) a b xs ys)
    (W : BoundedWiring (Γ := Cell) a b xs ys) (u : Label → Bool) :
    boundedBits (h.mpr W) u = boundedBits W u := by
  subst a' b' xs' ys'
  rfl

/-- Prefix-filter routing expands to the exact canonical colored reordering word. -/
theorem expand_program {Label : Type} [DecidableEq Label] (wire : Label → Wire)
    (hi : Function.Injective wire) (ys xs : List Label) (hp : xs.Perm ys)
    (hn : xs.Nodup) (k : ℕ) :
    expand (RoutingData.program ⟨ys.map wire, xs.map wire, k⟩) =
      (planarizeAlong Cell.expand
        (reorder (Γ := Cell) (fun a => (wire a).color) ys xs hp).diagram).toWord Prim.interp k := by
  change _ = boundedWord (reorderBounded (Γ := Cell) (fun a => (wire a).color) ys xs hp) k
  induction ys generalizing xs k with
  | nil =>
    obtain rfl := List.perm_nil.1 hp
    rfl
  | cons y ys ih =>
    generalize hs : splitAt y xs (hp.mem_iff.mpr (List.mem_cons_self ..)) = z
    obtain ⟨pre, post, rfl⟩ := z
    have hn' := (split_nodup hn).2
    rw [program_split wire hi ys pre post y hn k]
    rw [expand_append]
    rw [expand_pull wire pre y (post.map (fun a => (wire a).color))]
    have ht : (pre ++ post).Perm ys := (List.perm_middle.symm.trans hp).cons_inv
    rw [ih _ ht hn' (k + 1)]
    conv_rhs => unfold reorderBounded; rw [hs]
    dsimp only
    rw [boundedWord_transport_rev (by simp only [List.map_append, List.map_cons]) rfl rfl rfl]
    change _ =
      (planarizeAlong Cell.expand
        ((Wiring.moveLeft (Γ := Cell) (wire y).color y
          (post.map (fun a => (wire a).color)) post (List.length_map ..).symm
          (pre.map (fun a => (wire a).color)) pre (List.length_map ..).symm).comp
          ((Wiring.id [(wire y).color] [y] rfl).tensor _)).diagram).toWord Prim.interp k
    change _ =
      (planarizeAlong Cell.expand (Diagram.moveLeft (Γ := Cell)
        (pre.map (fun a => (wire a).color)) (wire y).color
        (post.map (fun a => (wire a).color)))).toWord Prim.interp k ++
      boundedWord _ (k + 1)
    rw [boundedWord_transport (List.map_append) rfl rfl rfl]

/-- Routing serializes the actual canonical crossover configurations in creation order. -/
theorem configurationBits_program {Label : Type} [DecidableEq Label] (wire : Label → Wire)
    (hi : Function.Injective wire) (ys xs : List Label) (hp : xs.Perm ys)
    (hn : xs.Nodup) (k : ℕ) :
    configurationBits (RoutingData.program ⟨ys.map wire, xs.map wire, k⟩) =
      extendedBits (reorder (Γ := Cell) (fun a => (wire a).color) ys xs hp).diagram
        ((fun a => (wire a).bit) ∘ (reorder (Γ := Cell)
          (fun a => (wire a).color) ys xs hp).labeling.label) := by
  change _ = boundedBits (reorderBounded (Γ := Cell) (fun a => (wire a).color) ys xs hp)
    (fun a => (wire a).bit)
  induction ys generalizing xs k with
  | nil =>
    obtain rfl := List.perm_nil.1 hp
    rfl
  | cons y ys ih =>
    generalize hs : splitAt y xs (hp.mem_iff.mpr (List.mem_cons_self ..)) = z
    obtain ⟨pre, post, rfl⟩ := z
    have hn' := (split_nodup hn).2
    rw [program_split wire hi ys pre post y hn k]
    rw [configurationBits_append, bits_pull wire pre post y k]
    have ht : (pre ++ post).Perm ys := (List.perm_middle.symm.trans hp).cons_inv
    rw [ih _ ht hn' (k + 1)]
    conv_rhs => unfold reorderBounded; rw [hs]
    dsimp only
    rw [boundedBits_transport_rev (by simp only [List.map_append, List.map_cons]) rfl rfl rfl]
    change _ = labelledBits
      ((Labeling.moveLeft (Γ := Cell) (wire y).color y
        (post.map (fun a => (wire a).color)) post (List.length_map ..).symm
        (pre.map (fun a => (wire a).color)) pre (List.length_map ..).symm).comp
        ((Labeling.id [(wire y).color] [y] rfl).tensor _)) (fun a => (wire a).bit)
    rw [labelledBits_comp, labelledBits_tensor, labelledBits_id, List.nil_append]
    change _ = labelledBits _ (fun a => (wire a).bit) ++ boundedBits _ (fun a => (wire a).bit)
    rw [boundedBits_transport (List.map_append) rfl rfl rfl]

end Cslib.Complexity.NCL.Planar.Embedding.PolyTime
