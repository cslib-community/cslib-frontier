/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Alternation.Savitch
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Combinators.ZipTransducer
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Combinators.Transducer
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Streaming

/-!
# The endpoints of Savitch's midpoint game

A play of Savitch's midpoint game (`Cslib.Reachability.midpointGame`) on words of width `w` and
`i` levels ends with a pair of endpoints, whose edge test decides the play. The pair depends on
two levels only: the left endpoint is the midpoint chosen at the last level whose half is `true`,
or the initial left endpoint if there is none, and the right endpoint is the midpoint chosen at
the last level whose half is `false`, or the initial right endpoint if there is none
(`Cslib.Reachability.midpointGame_eq_reach_lastMidpoint`).

The midpoint of the last level with a given half is extracted from any moves `z` in time linear in
the number of moves, `O((2 * w + 2) * i + w + |z|)`, by a native multi-tape machine
(`Cslib.Reachability.computableInO_lastMidpoint`). The moves are padded or cut to the length of the
game by a zip transducer (`Cslib.Reachability.padZip`); then the level marks are written in one
streaming pass (`Cslib.Reachability.levelMarks`), the moves are reversed, and a finite-state zip
transducer reads the marks and the reversed moves in lockstep (`Cslib.Reachability.endpointZip`),
copying the first level, from the end, with the wanted half. The moves are read a constant number of
times, not once per level: re-reading the remaining moves at every level would take order
`w * i ^ 2` steps. The word this endpoint machine computes is `Cslib.Reachability.endpointWord`.

This is a step toward `NSPACE(s) ⊆ ATIME(s ^ 2)` [Chandra, Kozen and
Stockmeyer][ChandraKozenStockmeyer1981], which
`Cslib.Complexity.NSPACE_subset_ATIME_sq_of_timeConstructible` assembles for a time-constructible
`s` (#4086) with the codes of the initial and accepting views and the edge test
`Cslib.Reachability.reach ntm.codeEdge _ 0` of the final endpoints.

## Main definitions

* `Cslib.Reachability.lastMidpoint`: the midpoint of the last level with a given half.
* `Cslib.Reachability.levelMarks`: the level marks, read backwards.
* `Cslib.Reachability.endpointZip`: the zip transducer copying the midpoint.
* `Cslib.Reachability.endpointWord`: the word the endpoint machine computes.
* `Cslib.Reachability.padZip`: the zip transducer padding or cutting the moves to the marks.

## Main results

* `Cslib.Reachability.lastMidpoint_eq_none_iff`, `Cslib.Reachability.lastMidpoint_eq_some_iff`:
  `lastMidpoint` is the midpoint of the last level with the given half.
* `Cslib.Reachability.iterate_midpointStep`: the endpoints after `i` levels.
* `Cslib.Reachability.midpointGame_eq_reach_lastMidpoint`: the midpoint game is the edge test of
  the midpoints of the last levels with each half.
* `Cslib.Reachability.lastMidpoint_congr`: `lastMidpoint` reads only the moves of its levels.
* `Cslib.Reachability.computableInO_lastMidpoint`: the midpoint of the last level with a given
  half, on any moves, within time and space linear in the number of moves.

## References

* [A. K. Chandra, D. C. Kozen, L. J. Stockmeyer, *Alternation*][ChandraKozenStockmeyer1981]
-/

@[expose] public section

namespace Cslib.Reachability

open Cslib.Complexity

variable {edge : List Bool → List Bool → Bool} {w : ℕ}

/-! ### The endpoints of the midpoint game -/

/-- The midpoint chosen at the last of the first `i` levels of the midpoint game on words of width
`w` whose half is `d`, if there is one. A level takes `2 * w + 2` moves: its midpoint is
`Cslib.Reachability.midpointMoves w` of the moves from its start, and its half is its last move. -/
def lastMidpoint (w : ℕ) : ℕ → List Bool → Bool → Option (List Bool)
  | 0, _, _ => none
  | i + 1, z, d => (lastMidpoint w i (z.drop (2 * w + 2)) d).or
      (if z.getD (2 * w + 1) false = d then some (midpointMoves w z) else none)

/-- Level `j` of the moves after the first level is level `j + 1` of the moves: its half. -/
private theorem getD_drop_level (z : List Bool) (j k : ℕ) :
    (z.drop (2 * w + 2)).getD ((2 * w + 2) * j + k) false =
      z.getD ((2 * w + 2) * (j + 1) + k) false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.mul_succ, Nat.add_assoc,
    Nat.add_comm (2 * w + 2)]

/-- Level `j` of the moves after the first level is level `j + 1` of the moves: its moves. -/
private theorem drop_drop_level (z : List Bool) (j : ℕ) :
    (z.drop (2 * w + 2)).drop ((2 * w + 2) * j) = z.drop ((2 * w + 2) * (j + 1)) := by
  rw [List.drop_drop, Nat.mul_succ, Nat.add_comm]

/-- **No level with half `d`.** `lastMidpoint w i z d` is `none` exactly when no level `j < i` of
the moves `z` has half `d`; the half of level `j` is the move `(2 * w + 2) * j + (2 * w + 1)`. -/
theorem lastMidpoint_eq_none_iff {i : ℕ} {z : List Bool} {d : Bool} :
    lastMidpoint w i z d = none ↔ ∀ j < i, z.getD ((2 * w + 2) * j + (2 * w + 1)) false ≠ d := by
  induction i generalizing z with
  | zero => simp [lastMidpoint]
  | succ i ih =>
    simp only [lastMidpoint, Option.or_eq_none_iff, ih, getD_drop_level, ite_eq_right_iff,
      reduceCtorEq, imp_false, Nat.forall_lt_succ_left, Nat.mul_zero, Nat.zero_add, and_comm]

/-- **The midpoint of the last level with half `d`.** `lastMidpoint w i z d` is `some m` exactly
when some level `j < i` of the moves `z` has half `d`, no later level `j' < i` has half `d`, and `m`
is the midpoint of level `j`, that is `Cslib.Reachability.midpointMoves w` of the moves from its
start `(2 * w + 2) * j`. -/
theorem lastMidpoint_eq_some_iff {i : ℕ} {z : List Bool} {d : Bool} {m : List Bool} :
    lastMidpoint w i z d = some m ↔ ∃ j < i, z.getD ((2 * w + 2) * j + (2 * w + 1)) false = d ∧
      midpointMoves w (z.drop ((2 * w + 2) * j)) = m ∧
      ∀ j', j < j' → j' < i → z.getD ((2 * w + 2) * j' + (2 * w + 1)) false ≠ d := by
  induction i generalizing z with
  | zero => simp [lastMidpoint]
  | succ i ih =>
    simp only [lastMidpoint, Option.or_eq_some_iff, ih, lastMidpoint_eq_none_iff,
      getD_drop_level, drop_drop_level, Nat.exists_lt_succ_left, Nat.mul_zero, Nat.zero_add,
      List.drop_zero]
    refine ⟨?_, ?_⟩
    · rintro (⟨j, hj, h1, h2, h3⟩ | ⟨hn, hs⟩)
      · exact .inr ⟨j, hj, h1, h2, fun
          | 0, hj', _ => by omega
          | k + 1, hj', hj'' => h3 k (by omega) (by omega)⟩
      · obtain ⟨hd, rfl⟩ : z.getD (2 * w + 1) false = d ∧ midpointMoves w z = m := by simpa using hs
        exact .inl ⟨hd, rfl, fun
          | 0, hj', _ => by omega
          | k + 1, _, hj'' => hn k (by omega)⟩
    · rintro (⟨h1, rfl, h3⟩ | ⟨j, hj, h1, h2, h3⟩)
      · exact .inr ⟨fun k hk => h3 (k + 1) (Nat.succ_pos _) (by omega), ite_eq_left h1⟩
      · exact .inl ⟨j, hj, h1, h2, fun k hk hk' => h3 (k + 1) (by omega) (by omega)⟩

/-- **The endpoints after `i` levels.** After `i` levels of the midpoint game from `u` and `v`,
the left endpoint is the midpoint of the last level whose half is `true`, or `u`, and the right
endpoint is the midpoint of the last level whose half is `false`, or `v`. -/
theorem iterate_midpointStep (i : ℕ) (u v z : List Bool) :
    (midpointStep w)^[i] (u, v, z) =
      ((lastMidpoint w i z true).getD u, (lastMidpoint w i z false).getD v,
        z.drop ((2 * w + 2) * i)) := by
  induction i generalizing u v z with
  | zero => simp [lastMidpoint]
  | succ i ih =>
    rw [Function.iterate_succ_apply, lastMidpoint, lastMidpoint]
    change (midpointStep w)^[i] (if z.getD (2 * w + 1) false then
        (midpointMoves w z, v, z.drop (2 * w + 2))
      else (u, midpointMoves w z, z.drop (2 * w + 2))) = _
    cases z.getD (2 * w + 1) false <;>
      simp only [Bool.false_eq_true, ↓reduceIte, ih, drop_drop_level] <;>
      cases lastMidpoint w i (z.drop (2 * w + 2)) true <;>
      cases lastMidpoint w i (z.drop (2 * w + 2)) false <;> rfl

/-- **The midpoint game depends on two levels.** The existential player wins a play of the
midpoint game at level `i` between `u` and `v` exactly when the edge test accepts the midpoint of
the last level whose half is `true` (or `u`) and the midpoint of the last level whose half is
`false` (or `v`). -/
theorem midpointGame_eq_reach_lastMidpoint (i : ℕ) (u v z : List Bool) :
    midpointGame edge w i u v z =
      reach edge w 0 ((lastMidpoint w i z true).getD u) ((lastMidpoint w i z false).getD v) := by
  rw [midpointGame_eq_iterate, iterate_midpointStep]

/-! ### The endpoint machine -/

open _root_.Turing _root_.Turing.MultiTapeTM

/-- The level marks of `i` levels of `2 * w + 2` moves, read from the last move backwards: for each
level, `true` at its half, then `false` at its other `2 * w + 1` moves. -/
def levelMarks (w i : ℕ) : List Bool :=
  ((List.range i).map fun _ => true :: List.replicate (2 * w + 1) false).flatten

/-- The states of the endpoint scan, which reads the levels from the last one backwards. -/
inductive EndpointState
  /-- No level with the wanted half yet. -/
  | seek
  /-- At the move of the existential player after the half of the level found. -/
  | skip
  /-- Copying the level found, at a move of the universal player. -/
  | univ
  /-- Copying the level found, at a bit of its midpoint. -/
  | mid
  /-- Past the level found. -/
  | done
  deriving DecidableEq

instance : Finite EndpointState :=
  Finite.of_surjective (fun n : Fin 5 => [EndpointState.seek, .skip, .univ, .mid, .done][n])
    fun q => by
      cases q
      exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩, ⟨4, rfl⟩]

/-- **The endpoint scan** for the half `d`: a zip transducer reading the level marks and the
reversed moves in lockstep. It emits the bits of the midpoint of the first level read, that is the
last level of the game, whose half is `d`, last bit first, and then `true`; it emits nothing if no
level has half `d`. -/
def endpointZip (d : Bool) : ZipTransducer EndpointState where
  q₀ := .seek
  step
    | .seek, (some true, some b) => (if b = d then .skip else .seek, [])
    | .seek, _ => (.seek, [])
    | .skip, _ => (.univ, [])
    | .univ, (some true, _) => (.done, [])
    | .univ, _ => (.mid, [])
    | .mid, (_, b) => (.univ, [b.getD false])
    | .done, _ => (.done, [])
  final
    | .seek => []
    | _ => [true]
  length_step_le q x := by
    rcases x with ⟨_ | _ | _, _ | _ | _⟩ <;> cases q <;> simp
  length_final_le q := by cases q <;> simp

/-- Copies a word. -/
private def copyT : Transducer Bool Unit where
  q₀ := ()
  step _ b := ((), [b])
  final _ := []
  length_step_le _ _ := by simp
  length_final_le _ := by simp

/-- `copyT` copies its input. -/
private theorem copyT_run (l : List Bool) : copyT.run () l = l := by
  induction l with
  | nil => rfl
  | cons b l ih => exact congrArg (b :: ·) ih

/-- Emits nothing. -/
private def nilT : Transducer Bool Unit where
  q₀ := ()
  step _ _ := ((), [])
  final _ := []
  length_step_le _ _ := by simp
  length_final_le _ := by simp

/-- `nilT` emits nothing. -/
private theorem nilT_run (l : List Bool) : nilT.run () l = [] := by
  induction l with
  | nil => rfl
  | cons b l ih => exact ih

/-- On the unary `n`, writes `true` and then `2 * n + 1` times `false`. -/
private def blockT : Transducer Bool Bool where
  q₀ := false
  step q _ := (true, if q then [false, false] else [true, false])
  final q := if q then [false, false] else [true, false]
  length_step_le q _ := by cases q <;> simp
  length_final_le q := by cases q <;> simp

/-- After the first symbol, `blockT` writes two `false`s per symbol and two at the end. -/
private theorem blockT_run_true (n : ℕ) :
    blockT.run true (List.replicate n true) = List.replicate (2 * n + 2) false := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa [List.replicate_succ, Transducer.run_cons, blockT, Nat.mul_succ] using
      congrArg (false :: false :: ·) ih

/-- `blockT` writes one level of the level marks. -/
private theorem blockT_run (n : ℕ) :
    blockT.run false (List.replicate n true) = true :: List.replicate (2 * n + 1) false := by
  cases n with
  | zero => rfl
  | succ n =>
    simpa [List.replicate_succ, Transducer.run_cons, blockT, Nat.mul_succ] using
      congrArg (true :: false :: ·) (blockT_run_true n)

/-- The level marks have one mark per move. -/
private theorem length_levelMarks (w i : ℕ) : (levelMarks w i).length = (2 * w + 2) * i := by
  simp [levelMarks, mul_comm]

/-- The level marks are written in one streaming pass, in time linear in their length. -/
private theorem computableInO_levelMarks :
    ComputableInO (fun p : ℕ × ℕ => levelMarks p.1 p.2) (encPair encUnary encUnary) encBits
      (fun p => (2 * p.1 + 2) * p.2 + p.1) (fun p => (2 * p.1 + 2) * p.2 + p.1) := by
  have hnext : ComputableInTimeAndSpace (id : ℕ → ℕ) encUnary encUnary
      (fun n => 4 * (encUnary n).length + 8) (fun _ => 0) :=
    copyT.computableInTimeAndSpace fun n => (copyT_run _).symm
  have hemit : ComputableInTimeAndSpace (fun n : ℕ => true :: List.replicate (2 * n + 1) false)
      encUnary encBits (fun n => 4 * (encUnary n).length + 8) (fun _ => 0) :=
    blockT.computableInTimeAndSpace fun n => (blockT_run n).symm
  have hfinish : ComputableInTimeAndSpace (fun _ : ℕ => ([] : List Bool)) encUnary encBits
      (fun n => 4 * (encUnary n).length + 8) (fun _ => 0) :=
    nilT.computableInTimeAndSpace fun n => (nilT_run _).symm
  obtain ⟨c, hc⟩ := ComputableInTimeAndSpace.iterate_unary_stream_sum hnext hemit hfinish
    (R := fun x _ => 10 * x.1 + 20) (Q := fun _ => 0) (B := fun x => x.1)
    (fun x i _ => by simp; omega) (fun _ _ _ => le_rfl)
    (fun x i _ => by simp)
  simp only [Function.iterate_id, id_eq, List.append_nil, Finset.sum_const, Finset.card_range,
    smul_eq_mul] at hc
  refine ComputableInO.of_bounds hc (20 * c + 20) (fun x => ?_) (fun x => ?_) (fun x => ?_)
  · simp only [encUnary_apply, List.length_replicate]
    have key : 4 * x.1 + 8 + x.2 * (10 * x.1 + 20) + x.1 + 1 ≤
        20 * ((2 * x.1 + 2) * x.2 + x.1 + 1) := by nlinarith
    calc c * (4 * x.1 + 8 + x.2 * (10 * x.1 + 20) + x.1 + 1)
        ≤ c * (20 * ((2 * x.1 + 2) * x.2 + x.1 + 1)) := Nat.mul_le_mul_left _ key
      _ ≤ (20 * c + 20) * ((2 * x.1 + 2) * x.2 + x.1 + 1) := by nlinarith
  · calc c * (0 + 0 + x.1 + 1) ≤ (20 * c + 20) * (x.1 + 1) := by
          simp only [zero_add]; exact Nat.mul_le_mul_right _ (by omega)
      _ ≤ (20 * c + 20) * ((2 * x.1 + 2) * x.2 + x.1 + 1) :=
          Nat.mul_le_mul_left _ (by linarith [Nat.zero_le ((2 * x.1 + 2) * x.2)])
  · simp only [encBits_apply, length_levelMarks]
    calc (2 * x.1 + 2) * x.2 ≤ (2 * x.1 + 2) * x.2 + x.1 + 1 := by omega
      _ ≤ (20 * c + 20) * ((2 * x.1 + 2) * x.2 + x.1 + 1) := Nat.le_mul_of_pos_left _ (by omega)


/-- A zip transducer emits at most two symbols per pair of digits, and two at the end. -/
private theorem length_run_le {Q : Type} (τ : ZipTransducer Q) (q : Q) (u v : List Bool) :
    (τ.run q u v).length ≤ 2 * (u.length + v.length) + 2 := by
  induction hn : u.length + v.length using Nat.strong_induction_on generalizing q u v with
  | _ n ih =>
    rcases u with _ | ⟨a, u⟩ <;> rcases v with _ | ⟨b, v⟩
    · simpa only [ZipTransducer.run_nil_nil] using (τ.length_final_le q).trans (Nat.le_add_left _ _)
    all_goals
      simp only [ZipTransducer.run_nil_cons, ZipTransducer.run_cons_nil,
        ZipTransducer.run_cons_cons, List.length_append]
      refine (Nat.add_le_add (τ.length_step_le _ _) (ih _ ?_ _ _ _ rfl)).trans ?_
      all_goals
        simp only [List.length_cons, List.length_nil] at hn ⊢
        omega

/-- The word computed by the endpoint machine for the half `d`, on the width `w`, the number `i`
of levels and the moves `z`: the endpoint scan of the level marks and the reversed moves, reversed.
On moves of the length of the game it encodes `Cslib.Reachability.lastMidpoint w i z d`. -/
def endpointWord (d : Bool) : ℕ × ℕ × List Bool → List Bool
  | (w, i, z) => ((endpointZip d).run .seek (levelMarks w i) z.reverse).reverse

/-- The midpoint of a level read from its moves, one universal move and one midpoint bit at a
time. -/
private theorem midpointMoves_cons_cons' (w : ℕ) (x y : Bool) (z : List Bool) :
    midpointMoves (w + 1) (x :: y :: z) = x :: midpointMoves w z := by
  simp [midpointMoves, List.range_succ_eq_map, Nat.mul_succ]

/-- The level marks of `i + 1` levels: those of `i` levels, then those of one more level. -/
private theorem levelMarks_succ (w i : ℕ) :
    levelMarks w (i + 1) = levelMarks w i ++ true :: List.replicate (2 * w + 1) false := by
  simp [levelMarks, List.range_succ]

/-- Before the level found, the endpoint scan skips the moves at `false` marks. -/
private theorem run_seek_replicate (d : Bool) (b e v : List Bool) {n : ℕ} (hv : v.length = n) :
    (endpointZip d).run .seek (List.replicate n false ++ b) (v ++ e) =
      (endpointZip d).run .seek b e := by
  subst hv
  induction v with
  | nil => rfl
  | cons _ v ih => simpa [endpointZip, List.replicate_succ] using ih

/-- Past the level found, the endpoint scan emits nothing. -/
private theorem run_done_append (d : Bool) (b e : List Bool) :
    ∀ u v : List Bool, u.length = v.length →
      (endpointZip d).run .done (u ++ b) (v ++ e) = (endpointZip d).run .done b e
  | [], [], _ => rfl
  | _ :: u, _ :: v, h => by
    simpa [endpointZip] using run_done_append d b e u v (by simpa using h)

/-- In the level found, the endpoint scan copies its midpoint, last bit first. -/
private theorem run_univ_replicate (d : Bool) (t : List Bool) (w : ℕ) :
    ∀ (b e m : List Bool), m.length = 2 * w →
      (endpointZip d).run .univ (List.replicate (2 * w) false ++ b) (m.reverse ++ e) =
        (midpointMoves w (m ++ t)).reverse ++ (endpointZip d).run .univ b e := by
  induction w with
  | zero =>
    intro b e m h
    obtain rfl : m = [] := List.eq_nil_of_length_eq_zero h
    simp [midpointMoves]
  | succ w ih =>
    intro b e m h
    rcases m with _ | ⟨x, _ | ⟨y, m⟩⟩
    · simp at h
    · simp at h; omega
    · have h1 : List.replicate (2 * (w + 1)) false ++ b =
          List.replicate (2 * w) false ++ false :: false :: b := by
        simp [Nat.mul_succ, List.replicate_add]
      have h2 : (x :: y :: m).reverse ++ e = m.reverse ++ y :: x :: e := by simp
      rw [h1, h2, ih _ _ m (by simp at h; omega)]
      simp [endpointZip, midpointMoves_cons_cons']

/-- Before the level found, the endpoint scan reads one level backwards: it copies its midpoint
if its half is `d`, and skips it otherwise. -/
private theorem run_seek_level (d x h : Bool) (b e m t : List Bool) (hm : m.length = 2 * w) :
    (endpointZip d).run .seek (true :: List.replicate (2 * w + 1) false ++ b)
        (h :: x :: m.reverse ++ e) =
      if h = d then (midpointMoves w (m ++ t)).reverse ++ (endpointZip d).run .univ b e
      else (endpointZip d).run .seek b e := by
  by_cases hd : h = d
  · simpa [endpointZip, hd, List.replicate_succ] using run_univ_replicate d t w b e m hm
  · simpa [endpointZip, hd] using
      run_seek_replicate d b e (x :: m.reverse) (n := 2 * w + 1) (by simp [hm])

/-- Once the level is found, the endpoint scan emits nothing on a further level. -/
private theorem run_found_level (d x h : Bool) (b e m : List Bool) (hm : m.length = 2 * w)
    {q : EndpointState} (hq : q = .univ ∨ q = .done) :
    (endpointZip d).run q (true :: List.replicate (2 * w + 1) false ++ b)
        (h :: x :: m.reverse ++ e) = (endpointZip d).run .done b e := by
  rcases hq with rfl | rfl <;>
    simpa [endpointZip] using
      run_done_append d b e (List.replicate (2 * w + 1) false) (x :: m.reverse) (by simp [hm])

/-- The endpoint scan from `.seek` over the level marks and the reversed moves of `i` levels:
it emits nothing and stays in `.seek` if no level has half `d`, and otherwise emits the midpoint
of the last such level, reversed, and moves to `.univ` or `.done`. -/
private theorem run_seek_levelMarks (d : Bool) :
    ∀ (i : ℕ) (z : List Bool), z.length = (2 * w + 2) * i →
      (lastMidpoint w i z d = none ∧ ∀ b e, (endpointZip d).run .seek (levelMarks w i ++ b)
          (z.reverse ++ e) = (endpointZip d).run .seek b e) ∨
      ∃ m q, lastMidpoint w i z d = some m ∧ (q = .univ ∨ q = .done) ∧
        ∀ b e, (endpointZip d).run .seek (levelMarks w i ++ b) (z.reverse ++ e) =
          m.reverse ++ (endpointZip d).run q b e
  | 0, z, hz => by
    obtain rfl : z = [] := List.eq_nil_of_length_eq_zero (by simpa using hz)
    exact .inl ⟨rfl, fun b e => by simp [levelMarks]⟩
  | i + 1, z, hz => by
    obtain ⟨m, r, rfl, hm⟩ : ∃ m r, z = m ++ r ∧ m.length = 2 * w :=
      ⟨z.take (2 * w), z.drop (2 * w), (List.take_append_drop _ _).symm, by simp [hz]; nlinarith⟩
    rw [Nat.mul_succ] at hz
    rcases r with _ | ⟨x, _ | ⟨h, z'⟩⟩
    · simp at hz; omega
    · simp at hz; omega
    have hz' : z'.length = (2 * w + 2) * i := by simp at hz; omega
    have hlast : lastMidpoint w (i + 1) (m ++ x :: h :: z') d = (lastMidpoint w i z' d).or
        (if h = d then some (midpointMoves w (m ++ x :: h :: z')) else none) := by
      rw [lastMidpoint, List.drop_append, List.drop_eq_nil_of_le (by omega)]
      simp [List.getD_eq_getElem?_getD, hm]
    have hrun : ∀ b e, levelMarks w (i + 1) ++ b = levelMarks w i ++
        (true :: List.replicate (2 * w + 1) false ++ b) ∧
        (m ++ x :: h :: z').reverse ++ e = z'.reverse ++ (h :: x :: m.reverse ++ e) :=
      fun b e => ⟨by simp [levelMarks_succ], by simp⟩
    rcases run_seek_levelMarks d i z' hz' with ⟨hn, hseek⟩ | ⟨m', q, hs, hq, hseek⟩
    · by_cases hd : h = d
      · refine .inr ⟨midpointMoves w (m ++ x :: h :: z'), .univ, by rw [hlast, hn]; simp [hd],
          .inl rfl, fun b e => ?_⟩
        rw [(hrun b e).1, (hrun b e).2, hseek, run_seek_level d x h b e m (x :: h :: z') hm]
        simp [hd]
      · refine .inl ⟨by simp [hlast, hn, hd], fun b e => ?_⟩
        rw [(hrun b e).1, (hrun b e).2, hseek, run_seek_level d x h b e m [] hm]
        simp [hd]
    · refine .inr ⟨m', .done, by simp [hlast, hs], .inr rfl, fun b e => ?_⟩
      rw [(hrun b e).1, (hrun b e).2, hseek, run_found_level d x h b e m hm hq]

/-- **The endpoint machine finds the last level with a given half.** On moves of the length of the
midpoint game, `endpointWord d` encodes the midpoint of the last level whose half is `d`, as an
option. -/
private theorem endpointWord_eq (d : Bool) {i : ℕ} {z : List Bool}
    (hz : z.length = (2 * w + 2) * i) :
    endpointWord d (w, i, z) = encOption encBits (lastMidpoint w i z d) := by
  rcases run_seek_levelMarks d i z hz with ⟨hn, hseek⟩ | ⟨m, _, hs, rfl | rfl, hseek⟩
  · simpa [endpointWord, hn, ZipTransducer.run_nil_nil, endpointZip] using
      congrArg List.reverse (hseek [] [])
  all_goals
    simpa [endpointWord, hs, ZipTransducer.run_nil_nil, endpointZip, encBits_apply] using
      congrArg List.reverse (hseek [] [])

/-- **The endpoint machine runs in linear time.** The word `endpointWord d (w, i, z)` is computed
on a multi-tape machine within time and space `O((2 * w + 2) * i + w + |z|)`, linear in the number
`(2 * w + 2) * i` of moves of the midpoint game. -/
private theorem computableInO_endpointWord (d : Bool) :
    ComputableInO (endpointWord d) (encPair encUnary (encPair encUnary encBits)) encBits
      (fun p => (2 * p.1 + 2) * p.2.1 + p.1 + p.2.2.length)
      (fun p => (2 * p.1 + 2) * p.2.1 + p.1 + p.2.2.length) := by
  have hrev : ComputableInO List.reverse encBits encBits (fun l => (encBits l).length)
      (fun l => (encBits l).length) :=
    .of_bounds ComputableInTimeAndSpace.reverse_bits 2
      (fun l => by simp only [encBits_apply]; omega) (fun _ => by omega)
      (fun l => by simp only [encBits_apply, List.length_reverse]; omega)
  have hzip : ComputableInO (fun q : List Bool × List Bool => (endpointZip d).run .seek q.1 q.2)
      (encPair encBits encBits) encBits (fun q => (encPair encBits encBits q).length)
      (fun q => (encPair encBits encBits q).length) :=
    .of_bounds (endpointZip d).computableInTimeAndSpace_run 3 (fun q => by omega)
      (fun q => by simp only [length_encPair, encBits_apply]; omega)
      (fun q => (length_run_le (endpointZip d) .seek q.1 q.2).trans
        (by simp only [length_encPair, encBits_apply]; omega))
  have hpair := (ComputableInO.fst encUnary (encPair encUnary encBits)).prod
    (ComputableInO.snd encUnary (encPair encUnary encBits)).fst'
  have hmarks := computableInO_levelMarks.comp hpair
  have hz := hrev.comp_linear (ComputableInO.snd encUnary (encPair encUnary encBits)).snd'
  have h := hrev.comp_linear (hzip.comp_linear (hmarks.prod hz))
  refine h.mono 8 (fun p => ?_) (fun p => ?_) <;>
  · simp only [length_encPair, encUnary_apply, encBits_apply, List.length_replicate]
    nlinarith

/-- The pad scan: one move per mark, `false` past the end of the moves, nothing past the marks. -/
def padZip : ZipTransducer Unit where
  q₀ := ()
  step _ x := ((), match x with
    | (some _, b) => [b.getD false]
    | (none, _) => [])
  final _ := []
  length_step_le _ x := by rcases x with ⟨_ | _, _ | _⟩ <;> simp
  length_final_le _ := by simp

/-- The pad scan reads the moves at the positions of the marks, `false` past their end. -/
theorem padZip_run (u z : List Bool) :
    padZip.run () u z = (List.range u.length).map fun p => z.getD p false := by
  induction u generalizing z with
  | nil =>
    induction z with
    | nil => simp [padZip]
    | cons _ z ih => simpa [padZip] using ih
  | cons _ u ih =>
    have h := ih z.tail
    cases z <;> simpa [padZip, List.range_succ_eq_map, Function.comp_def] using h

/-- `lastMidpoint w i z d` reads only the first `(2 * w + 2) * i` moves of `z`. -/
theorem lastMidpoint_congr {i : ℕ} {z z' : List Bool} {d : Bool}
    (h : ∀ p < (2 * w + 2) * i, z.getD p false = z'.getD p false) :
    lastMidpoint w i z d = lastMidpoint w i z' d := by
  induction i generalizing z z' with
  | zero => rfl
  | succ i ih =>
    have hd : ∀ p < (2 * w + 2) * i,
        (z.drop (2 * w + 2)).getD p false = (z'.drop (2 * w + 2)).getD p false := fun p hp => by
      simpa only [List.getD_eq_getElem?_getD, List.getElem?_drop] using
        h _ (by rw [Nat.mul_succ]; omega)
    have hm : midpointMoves w z = midpointMoves w z' :=
      List.map_congr_left fun j hj => h _ (by simp at hj; rw [Nat.mul_succ]; omega)
    simp only [lastMidpoint, ih hd, hm, h (2 * w + 1) (by rw [Nat.mul_succ]; omega)]

/-- A machine computes any function with the same encoded outputs, within the same bounds. -/
private theorem computableInO_of_encOut_eq {α β γ : Type*} {encIn : α ↪ List Bool}
    {encOut : β ↪ List Bool} {encOut' : γ ↪ List Bool} {f : α → β} {g : α → γ} {T S : α → ℕ}
    (h : ComputableInO f encIn encOut T S) (he : ∀ a, encOut (f a) = encOut' (g a)) :
    ComputableInO g encIn encOut' T S := by
  obtain ⟨c, ⟨k, State, hfin, tm, htm⟩, hl⟩ := h
  exact ⟨c, ⟨k, State, hfin, tm, fun a => he a ▸ htm a⟩, fun a => he a ▸ hl a⟩

/-- **The midpoint of the last level with a given half, in linear time.** On any moves `z`, the
midpoint of the last of the first `i` levels whose half is `d`, as an option, is computed on a
multi-tape machine within time and space `O((2 * w + 2) * i + w + |z|)`: the moves are padded or
cut to the length of the game by the pad scan, and then the endpoint machine runs. -/
theorem computableInO_lastMidpoint (d : Bool) :
    ComputableInO (fun ((w, i, z) : ℕ × ℕ × List Bool) => lastMidpoint w i z d)
      (encPair encUnary (encPair encUnary encBits)) (encOption encBits)
      (fun ((w, i, z) : ℕ × ℕ × List Bool) => (2 * w + 2) * i + w + z.length)
      (fun ((w, i, z) : ℕ × ℕ × List Bool) => (2 * w + 2) * i + w + z.length) := by
  have hzip : ComputableInO (fun q : List Bool × List Bool => padZip.run () q.1 q.2)
      (encPair encBits encBits) encBits (fun q => (encPair encBits encBits q).length)
      (fun q => (encPair encBits encBits q).length) :=
    .of_bounds padZip.computableInTimeAndSpace_run 3 (fun q => by omega)
      (fun q => by simp only [length_encPair, encBits_apply]; omega)
      (fun q => by
        simp only [padZip_run, length_encPair, encBits_apply, List.length_map, List.length_range]
        omega)
  have hfst := ComputableInO.fst encUnary (encPair encUnary encBits)
  have hsnd := ComputableInO.snd encUnary (encPair encUnary encBits)
  have hmarks := computableInO_levelMarks.comp (hfst.prod hsnd.fst')
  have hpad := hfst.prod (hsnd.fst'.prod (hzip.comp_linear (hmarks.prod hsnd.snd')))
  have h := computableInO_of_encOut_eq ((computableInO_endpointWord d).comp hpad)
    (g := fun ((w, i, z) : ℕ × ℕ × List Bool) => lastMidpoint w i z d)
    (encOut' := encOption encBits) fun ⟨w, i, z⟩ => by
      simp only [Function.comp_apply, encBits_apply]
      rw [endpointWord_eq d (by simp [padZip_run, length_levelMarks])]
      exact congrArg _ (lastMidpoint_congr fun p hp => by
        simp [padZip_run, List.getD_eq_getElem?_getD, length_levelMarks, hp])
  refine h.mono 40 (fun ⟨w, i, z⟩ => ?_) (fun ⟨w, i, z⟩ => ?_) <;>
  · simp only [Function.comp_apply, padZip_run, length_encPair, encUnary_apply, encBits_apply,
      List.length_replicate, List.length_map, List.length_range, length_levelMarks]
    nlinarith [Nat.zero_le (w * i)]

end Cslib.Reachability
