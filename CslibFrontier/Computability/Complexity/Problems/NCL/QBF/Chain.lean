/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.QBF.Exists
public import CslibFrontier.Computability.Complexity.Problems.NCL.QBF.Soundness
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Contract
import Mathlib.Data.List.Forall2

/-!
# Chains of quantifiers

A chain stacks the quantifiers of [HearnDemaine2005, Section 3.1] in binding order. Its two
control wires are followed by a tail of previously introduced literal wires. Each quantifier
adds its positive and negative literal wires to that tail. Recursing with this extended tail
keeps the dependent boundary types definitionally equal, without casts. The literal pairs at
the bottom occur in reverse binding order; memory values are read in binding order.

## Main definitions

* `Cslib.Complexity.NCL.QBF.Quantifier`: the kind of a quantifier.
* `Cslib.Complexity.NCL.QBF.Chain.diagram`: the chain, with a tail of wires on its right.
* `Cslib.Complexity.NCL.QBF.Chain.control`: the satisfied or try wire at a cut of the chain.
* `Cslib.Complexity.NCL.QBF.Chain.memories`: the values of its variable latches.
* `Cslib.Complexity.NCL.QBF.Chain.literalValues`: canonical literal directions in physical order.
* `Cslib.Complexity.NCL.QBF.Chain.Truth`: quantify a matrix predicate over a prefix.

## Main results

* `Cslib.Complexity.NCL.QBF.Chain.try_of_sat`: a satisfied cut needs trying at that cut,
  provided this holds at the bottom of the chain.
* `Cslib.Complexity.NCL.QBF.Chain.take_memories_eq_of_step`: a tried cut freezes the values
  of all variables before it, even in a containing diagram.
* `Cslib.Complexity.NCL.QBF.Chain.truth_of_reachable`: a successful chain certifies the
  quantified matrix, assuming its terminal contract only at reachable configurations.
* `Cslib.Complexity.NCL.QBF.Chain.literals_of_try`: actual literal directions are bounded by
  the canonical literal directions of the current memories while the final try is active.

The terminal contract is a hypothesis of this module; `NCL.QBF.Matrix` derives it for the actual
CNF network. `NCL.QBF.Source` supplies the source-QBF bridge, and `NCL.QBF.Initial` constructs
inactive legal configurations. `NCL.QBF.Completeness` executes the actual body, and
`NCL.QBF.Circuit` closes its controls and supplies a fixed target configuration.

## References

* [R. A. Hearn and E. D. Demaine, *PSPACE-completeness of sliding-block puzzles and other
  problems through the nondeterministic constraint logic model of computation*][HearnDemaine2005]
-/

public section

namespace Cslib.Complexity.NCL.QBF

open Diagram

local notation "R" => Color.red
local notation "B" => Color.blue

/-- The kind of a quantifier in a circuit's prefix. -/
inductive Quantifier
  /-- Existential quantification. -/
  | ex
  /-- Universal quantification. -/
  | all
  deriving @[expose] DecidableEq, Repr

namespace Quantifier

/-- The diagram of a quantifier. -/
@[expose] def gadget : Quantifier → Diagram Gate [B, B] [B, B, R, R]
  | ex => existsGadget
  | all => forallGadget

/-- The variable latch's memory edge. -/
@[expose] def mem : (q : Quantifier) → q.gadget.Edge
  | ex => ExistsGadget.mem
  | all => ForallGadget.mem

private theorem tryIn_of_tryOut (q : Quantifier) {t : q.gadget.Edge → Bool}
    (ht : (q.gadget.graph Gate.interp).Legal t) (h : t (q.gadget.bottom 1) = true) :
    t (.inl 1) = true := by
  cases q
  · exact ExistsGadget.tryIn_of_tryOut ht h
  · exact ForallGadget.tryIn_of_tryOut ht h

private theorem satIn_of_satOut (q : Quantifier) {t : q.gadget.Edge → Bool}
    (ht : (q.gadget.graph Gate.interp).Legal t) (h : t (.inl 0) = false) :
    t (q.gadget.bottom 0) = false := by
  cases q
  · exact h
  · exact ForallGadget.satIn_of_satOut ht h

private theorem mem_eq_of_step (q : Quantifier) {a b : List Color} {D : Diagram Gate a b}
    (o : Occurrence q.gadget D) {s t : D.Edge → Bool} (h : (D.graph Gate.interp).Step s t)
    (htry : s (o.emb (q.gadget.bottom 1)) = true) : s (o.emb q.mem) = t (o.emb q.mem) := by
  cases q
  · exact ExistsGadget.mem_eq_of_step o h htry
  · exact ForallGadget.mem_eq_of_step o h htry

private theorem mem_of_pos (q : Quantifier) {t : q.gadget.Edge → Bool}
    (ht : (q.gadget.graph Gate.interp).Legal t) (htry : t (q.gadget.bottom 1) = true)
    (hp : t (q.gadget.bottom 2) = true) : t q.mem = true := by
  cases q
  · exact ExistsGadget.mem_of_pos ht htry hp
  · exact ForallGadget.mem_of_pos ht htry hp

private theorem mem_of_neg (q : Quantifier) {t : q.gadget.Edge → Bool}
    (ht : (q.gadget.graph Gate.interp).Legal t) (htry : t (q.gadget.bottom 1) = true)
    (hn : t (q.gadget.bottom 3) = true) : t q.mem = false := by
  cases q
  · exact ExistsGadget.mem_of_neg ht htry hn
  · exact ForallGadget.mem_of_neg ht htry hn

private theorem literals_le (q : Quantifier) {t : q.gadget.Edge → Bool}
    (ht : (q.gadget.graph Gate.interp).Legal t) (htry : t (q.gadget.bottom 1) = true) :
    List.Forall₂ (· ≤ ·) [t (q.gadget.bottom 2), t (q.gadget.bottom 3)] [t q.mem, !t q.mem] := by
  refine .cons ?_ (.cons ?_ .nil)
  · cases hp : t (q.gadget.bottom 2) with
    | false => exact Bool.false_le _
    | true => rw [q.mem_of_pos ht htry hp]
  · cases hn : t (q.gadget.bottom 3) with
    | false => exact Bool.false_le _
    | true => rw [q.mem_of_neg ht htry hn]; exact le_rfl

end Quantifier

namespace Chain

/-- The bottom boundary of a chain. Newly introduced literal pairs precede the existing tail. -/
@[expose] def boundary (r : List Color) : List Quantifier → List Color
  | [] => [B, B] ++ r
  | _ :: qs => boundary ([R, R] ++ r) qs

/-- Stack the quantifiers in binding order, carrying older literal wires on the right. -/
@[expose] def diagram (r : List Color) : (qs : List Quantifier) →
    Diagram Gate ([B, B] ++ r) (boundary r qs)
  | [] => .id _
  | q :: qs => (q.gadget.tensor (.id r)).comp (diagram ([R, R] ++ r) qs)

/-- A control wire at the top boundary. -/
@[expose] def input (r : List Color) (qs : List Quantifier) (j : Fin 2) : (diagram r qs).Edge :=
  .inl ⟨j, by simp only [List.length_append, List.length_cons, List.length_nil]; omega⟩

/-- The first quantifier as an occurrence in the chain. -/
@[expose] def headOcc (r : List Color) (q : Quantifier) (qs : List Quantifier) :
    Occurrence q.gadget (diagram r (q :: qs)) := .compLeft _ (.tensorLeft (.id r) .refl)

/-- The remaining quantifiers as an occurrence in the chain. -/
@[expose] def tailOcc (r : List Color) (q : Quantifier) (qs : List Quantifier) :
    Occurrence (diagram ([R, R] ++ r) qs) (diagram r (q :: qs)) := .compRight _ .refl

private theorem head_top (r : List Color) (q : Quantifier) (qs : List Quantifier) (j : Fin 2) :
    (headOcc r q qs).emb (.inl j) = input r (q :: qs) j := rfl

private theorem head_bottom (r : List Color) (q : Quantifier) (qs : List Quantifier) (j : Fin 2) :
    (headOcc r q qs).emb
        (q.gadget.bottom ⟨j, by simp only [List.length_cons, List.length_nil]; omega⟩) =
      (tailOcc r q qs).emb (input ([R, R] ++ r) qs j) := by
  exact congrArg (compLeft (q.gadget.tensor (.id r)) (diagram ([R, R] ++ r) qs))
    (bottom_tensor_left q.gadget (.id r)
      ⟨j, by simp only [List.length_cons, List.length_nil]; omega⟩).symm

private theorem head_top_trans (r : List Color) (q : Quantifier) (qs : List Quantifier)
    {a b : List Color} {D : Diagram Gate a b} (o : Occurrence (diagram r (q :: qs)) D) (j : Fin 2) :
    (o.trans (headOcc r q qs)).emb (.inl j) = o.emb (input r (q :: qs) j) :=
  (congrFun (o.emb_trans (headOcc r q qs)) (.inl j)).trans
    (congrArg o.emb (head_top r q qs j))

private theorem head_bottom_trans (r : List Color) (q : Quantifier) (qs : List Quantifier)
    {a b : List Color} {D : Diagram Gate a b} (o : Occurrence (diagram r (q :: qs)) D) (j : Fin 2) :
    (o.trans (headOcc r q qs)).emb
        (q.gadget.bottom ⟨j, by simp only [List.length_cons, List.length_nil]; omega⟩) =
      (o.trans (tailOcc r q qs)).emb (input ([R, R] ++ r) qs j) :=
  (congrFun (o.emb_trans (headOcc r q qs)) _).trans
    ((congrArg o.emb (head_bottom r q qs j)).trans
      (congrFun (o.emb_trans (tailOcc r q qs)) _).symm)

/-- The control wire at cut `n`: satisfied for `j = 0`, try for `j = 1`. Cuts beyond the end
refer to the final cut, so this interface needs no index casts. -/
@[expose] def control (r : List Color) : (qs : List Quantifier) → ℕ → Fin 2 → (diagram r qs).Edge
  | qs, 0, j => input r qs j
  | [], _ + 1, j => input r [] j
  | q :: qs, n + 1, j => (tailOcc r q qs).emb (control ([R, R] ++ r) qs n j)

private theorem control_zero (r : List Color) (qs : List Quantifier) (j : Fin 2) :
    control r qs 0 j = input r qs j := by
  cases qs <;> rfl

private theorem control_cons_succ (r : List Color) (q : Quantifier) (qs : List Quantifier)
    (n : ℕ) (j : Fin 2) : control r (q :: qs) (n + 1) j =
      (tailOcc r q qs).emb (control ([R, R] ++ r) qs n j) := rfl

/-- The values of the variable latches, in binding order. -/
@[expose]
def memories (r : List Color) : (qs : List Quantifier) → ((diagram r qs).Edge → Bool) → List Bool
  | [], _ => []
  | q :: qs, t => t ((headOcc r q qs).emb q.mem) ::
      memories ([R, R] ++ r) qs (t ∘ (tailOcc r q qs).emb)

private theorem first_try (r : List Color) (q : Quantifier) (qs : List Quantifier)
    {t : (diagram r (q :: qs)).Edge → Bool} (ht : ((diagram r (q :: qs)).graph Gate.interp).Legal t)
    (h : t ((tailOcc r q qs).emb (input ([R, R] ++ r) qs 1)) = true) :
    t (input r (q :: qs) 1) = true :=
  (congrArg t (head_top r q qs 1)).symm.trans <|
    q.tryIn_of_tryOut ((headOcc r q qs).legal ht)
      ((congrArg t (head_bottom r q qs 1)).trans h)

private theorem first_sat (r : List Color) (q : Quantifier) (qs : List Quantifier)
    {t : (diagram r (q :: qs)).Edge → Bool} (ht : ((diagram r (q :: qs)).graph Gate.interp).Legal t)
    (h : t (input r (q :: qs) 0) = false) :
    t ((tailOcc r q qs).emb (input ([R, R] ++ r) qs 0)) = false :=
  (congrArg t (head_bottom r q qs 0)).symm.trans <|
    q.satIn_of_satOut ((headOcc r q qs).legal ht) ((congrArg t (head_top r q qs 0)).trans h)

private theorem head_mem_eq_of_step (r : List Color) (q : Quantifier) (qs : List Quantifier)
    {a b : List Color} {D : Diagram Gate a b} (o : Occurrence (diagram r (q :: qs)) D)
    {s t : D.Edge → Bool} (h : (D.graph Gate.interp).Step s t)
    (htry : s (o.emb ((tailOcc r q qs).emb (input ([R, R] ++ r) qs 1))) = true) :
    s (o.emb ((headOcc r q qs).emb q.mem)) = t (o.emb ((headOcc r q qs).emb q.mem)) := by
  have hhead : s (o.emb ((headOcc r q qs).emb (q.gadget.bottom 1))) = true :=
    (congrArg (s ∘ o.emb) (head_bottom r q qs 1)).trans htry
  simpa only [Occurrence.emb_trans, Function.comp_def] using
    q.mem_eq_of_step (o.trans (headOcc r q qs)) h
      (by simpa only [Occurrence.emb_trans, Function.comp_def] using hhead)

/-- Trying at any cut requires trying at the start of the chain. -/
private theorem try_input_of_control : ∀ (qs : List Quantifier) (r : List Color) (n : ℕ)
    {t : (diagram r qs).Edge → Bool}, ((diagram r qs).graph Gate.interp).Legal t →
    t (control r qs n 1) = true → t (input r qs 1) = true
  | [], _, n, _, _, h => by cases n <;> exact h
  | _ :: _, _, 0, _, _, h => h
  | q :: qs, r, n + 1, _, ht, h =>
    first_try r q qs ht (try_input_of_control qs _ n ((tailOcc r q qs).legal ht) h)

/-- Trying at the bottom requires trying at every cut of the chain. -/
private theorem try_control_of_output : ∀ (qs : List Quantifier) (r : List Color) (n : ℕ)
    {t : (diagram r qs).Edge → Bool}, ((diagram r qs).graph Gate.interp).Legal t →
    t (control r qs qs.length 1) = true → t (control r qs n 1) = true
  | [], _, n, _, _, h => by cases n <;> exact h
  | q :: qs, r, 0, _, ht, h => by
    apply first_try r q qs ht
    simpa only [control_zero, Function.comp_def]
      using try_control_of_output qs _ 0 ((tailOcc r q qs).legal ht) h
  | q :: qs, r, n + 1, _, ht, h =>
    try_control_of_output qs _ n ((tailOcc r q qs).legal ht) h

/-- Satisfaction at any cut propagates to the bottom of the chain. -/
private theorem sat_output_of_control : ∀ (qs : List Quantifier) (r : List Color) (n : ℕ)
    {t : (diagram r qs).Edge → Bool}, ((diagram r qs).graph Gate.interp).Legal t →
    t (control r qs n 0) = false → t (control r qs qs.length 0) = false
  | [], _, n, _, _, h => by cases n <;> exact h
  | q :: qs, r, 0, _, ht, h =>
    sat_output_of_control qs _ 0 ((tailOcc r q qs).legal ht)
      (by simpa only [control_zero, Function.comp_def] using first_sat r q qs ht h)
  | q :: qs, r, n + 1, _, ht, h =>
    sat_output_of_control qs _ n ((tailOcc r q qs).legal ht) h

/-- **Admissibility at every cut**, assuming it at the final cut. This is the static
right-to-left induction of [HearnDemaine2005, Lemma 1]. -/
theorem try_of_sat (qs : List Quantifier) (r : List Color) (n : ℕ)
    {t : (diagram r qs).Edge → Bool} (ht : ((diagram r qs).graph Gate.interp).Legal t)
    (hadm : t (control r qs qs.length 0) = false → t (control r qs qs.length 1) = true)
    (h : t (control r qs n 0) = false) : t (control r qs n 1) = true :=
  try_control_of_output qs r n ht (hadm (sat_output_of_control qs r n ht h))

/-- **A tried cut freezes its prefix assignment.** Every move in any containing diagram keeps
the first `n` variable values while the try signal at cut `n` is active. -/
theorem take_memories_eq_of_step : ∀ (qs : List Quantifier) (r : List Color) (n : ℕ)
    {a b : List Color} {D : Diagram Gate a b} (o : Occurrence (diagram r qs) D)
    {s t : D.Edge → Bool}, (D.graph Gate.interp).Step s t →
    s (o.emb (control r qs n 1)) = true →
    (memories r qs (s ∘ o.emb)).take n = (memories r qs (t ∘ o.emb)).take n
  | [], _, _, _, _, _, _, _, _, _, _ => rfl
  | _ :: _, _, 0, _, _, _, _, _, _, _, _ => rfl
  | q :: qs, r, n + 1, _, _, _, o, s, t, h, htry => by
    have ht := o.legal h.legal_left
    have htail := try_input_of_control qs ([R, R] ++ r) n ((tailOcc r q qs).legal ht) htry
    have hm := head_mem_eq_of_step r q qs o h htail
    have ih := take_memories_eq_of_step qs ([R, R] ++ r) n (o.trans (tailOcc r q qs)) h
      (by simpa only [Occurrence.emb_trans, Function.comp_def, control_cons_succ] using htry)
    simpa only [memories, List.take_succ_cons, Occurrence.emb_trans, Function.comp_def]
      using congrArg₂ List.cons hm ih

/-- Canonical literal directions in physical wire order: innermost variable first, with its
positive direction followed by its negative direction. Memory values are in binding order. -/
@[expose]
def literalValues (values : List Bool) : List Bool := values.reverse.flatMap fun v => [v, !v]

private theorem literalValues_cons (value : Bool) (values : List Bool) :
    literalValues (value :: values) = literalValues values ++ [value, !value] := by
  simp [literalValues]

private theorem topList_controls (r : List Color) (qs : List Quantifier)
    (t : (diagram r qs).Edge → Bool) : (diagram r qs).topList t =
      t (input r qs 0) :: t (input r qs 1) :: ((diagram r qs).topList t).drop 2 := by
  simp [topList, List.ofFn_succ, input]

private theorem tail_topList (r : List Color) (q : Quantifier) (qs : List Quantifier)
    (t : (diagram r (q :: qs)).Edge → Bool) :
    (diagram ([R, R] ++ r) qs).topList (t ∘ (tailOcc r q qs).emb) =
      t ((headOcc r q qs).emb (q.gadget.bottom 0)) ::
      t ((headOcc r q qs).emb (q.gadget.bottom 1)) ::
      t ((headOcc r q qs).emb (q.gadget.bottom 2)) ::
      t ((headOcc r q qs).emb (q.gadget.bottom 3)) :: ((diagram r (q :: qs)).topList t).drop 2 := by
  let tr := t ∘ compLeft (q.gadget.tensor (.id r)) (diagram ([R, R] ++ r) qs)
  let rs := (Diagram.id r : Diagram Gate r r).topList (tr ∘ tensorRight q.gadget (.id r))
  have htop : (diagram r (q :: qs)).topList t =
      q.gadget.topList (t ∘ (headOcc r q qs).emb) ++ rs :=
    (topList_compLeft _ _ t).symm.trans (topList_tensor _ _ tr)
  have hbot : (diagram ([R, R] ++ r) qs).topList (t ∘ (tailOcc r q qs).emb) =
      q.gadget.botList (t ∘ (headOcc r q qs).emb) ++ rs :=
    (topList_compRight _ _ t).trans (botList_tensor _ _ tr)
  rw [htop, hbot]
  simp only [topList, botList, List.ofFn_succ, List.ofFn_zero, List.cons_append, List.nil_append,
    List.drop_succ_cons, List.drop_zero, Function.comp_def]
  rfl

private theorem tail_botList (r : List Color) (q : Quantifier) (qs : List Quantifier)
    (t : (diagram r (q :: qs)).Edge → Bool) :
    (diagram ([R, R] ++ r) qs).botList (t ∘ (tailOcc r q qs).emb) =
      (diagram r (q :: qs)).botList t := botList_compRight _ _ t

/-- The first two bottom directions are the final satisfied and try controls. This is a wiring
identity and requires no legality or activation assumption. -/
theorem botList_controls : ∀ (qs : List Quantifier) (r : List Color)
    (t : (diagram r qs).Edge → Bool), ∃ ls, (diagram r qs).botList t =
      t (control r qs qs.length 0) :: t (control r qs qs.length 1) :: ls
  | [], r, t => ⟨_, topList_controls r [] t⟩
  | q :: qs, r, t =>
    let ⟨ls, hls⟩ := botList_controls qs ([R, R] ++ r) (t ∘ (tailOcc r q qs).emb)
    ⟨ls, by simpa only [control_cons_succ, List.length_cons, Function.comp_def] using
      (tail_botList r q qs t).symm.trans hls⟩

private theorem literals_le_of_tail : ∀ (qs : List Quantifier) (r : List Color)
    {t : (diagram r qs).Edge → Bool}, ((diagram r qs).graph Gate.interp).Legal t →
    t (control r qs qs.length 1) = true → ∀ bounds : List Bool,
    List.Forall₂ (· ≤ ·) (((diagram r qs).topList t).drop 2) bounds →
    ∃ ls, (diagram r qs).botList t =
      t (control r qs qs.length 0) :: t (control r qs qs.length 1) :: ls ∧
      List.Forall₂ (· ≤ ·) ls (literalValues (memories r qs t) ++ bounds)
  | [], r, t, _, _, bounds, hb =>
    ⟨_, topList_controls r [] t, hb⟩
  | q :: qs, r, t, ht, htry, bounds, hb => by
    have hhead := try_control_of_output (q :: qs) r 1 ht htry
    have hpair := q.literals_le ((headOcc r q qs).legal ht)
      ((congrArg t (head_bottom r q qs 1)).trans
        (by simpa only [control_cons_succ, control_zero] using hhead))
    obtain ⟨ls, hls, hf⟩ := literals_le_of_tail qs ([R, R] ++ r) ((tailOcc r q qs).legal ht) htry
      _ (by
        rw [tail_topList]
        exact List.rel_append hpair hb)
    exact ⟨ls, by simpa only [control_cons_succ, List.length_cons, Function.comp_def] using
        (tail_botList r q qs t).symm.trans hls,
      by simpa only [memories, literalValues_cons, List.append_assoc, Function.comp_def] using hf⟩

/-- **Static consistency of the literal bundle.** While the final try wire is active, the bottom
tail is bounded by the canonical literals of the current latches followed by the incoming
directions of the older tail wires. -/
theorem literals_of_try (qs : List Quantifier) (r : List Color)
    {t : (diagram r qs).Edge → Bool} (ht : ((diagram r qs).graph Gate.interp).Legal t)
    (htry : t (control r qs qs.length 1) = true) :
    ∃ ls, (diagram r qs).botList t =
      t (control r qs qs.length 0) :: t (control r qs qs.length 1) :: ls ∧
      List.Forall₂ (· ≤ ·) ls
        (literalValues (memories r qs t) ++ ((diagram r qs).topList t).drop 2) :=
  literals_le_of_tail qs r ht htry _ (List.forall₂_refl _)

/-- Quantify a matrix predicate over the remaining variables, after the given values.
This evaluates a quantifier prefix against an arbitrary matrix, without introducing formula
syntax; the source formulas themselves use the upstream QBF type. -/
@[expose] def Truth (matrix : List Bool → Prop) : List Quantifier → List Bool → Prop
  | [], values => matrix values
  | .ex :: qs, values => ∃ value, Truth matrix qs (values ++ [value])
  | .all :: qs, values => ∀ value, Truth matrix qs (values ++ [value])

private theorem tail_inactive (r : List Color) (q : Quantifier) (qs : List Quantifier)
    {a b : List Color} {D : Diagram Gate a b} (o : Occurrence (diagram r (q :: qs)) D)
    {s : D.Edge → Bool} (hs : (D.graph Gate.interp).Legal s)
    (hstart : s (o.emb (input r (q :: qs) 1)) = false) :
    s ((o.trans (tailOcc r q qs)).emb (input ([R, R] ++ r) qs 1)) = false :=
  Bool.eq_false_iff.2 fun htry => Bool.noConfusion <| hstart.symm.trans <|
    first_try r q qs (o.legal hs)
      (by simpa only [Occurrence.emb_trans, Function.comp_def] using htry)

private theorem tail_context_eq (r : List Color) (q : Quantifier) (qs : List Quantifier)
    {a b : List Color} {D : Diagram Gate a b} (o : Occurrence (diagram r (q :: qs)) D)
    (context : (D.Edge → Bool) → List Bool) {s t : D.Edge → Bool}
    (h : (D.graph Gate.interp).Step s t)
    (hf : s (o.emb (input r (q :: qs) 1)) = true → context s = context t)
    (htry : s ((o.trans (tailOcc r q qs)).emb (input ([R, R] ++ r) qs 1)) = true) :
    context s ++ [s (o.emb ((headOcc r q qs).emb q.mem))] =
      context t ++ [t (o.emb ((headOcc r q qs).emb q.mem))] := by
  have htry' : s (o.emb ((tailOcc r q qs).emb (input ([R, R] ++ r) qs 1))) = true :=
    by simpa only [Occurrence.emb_trans, Function.comp_def] using htry
  exact congrArg₂ List.append (hf (first_try r q qs (o.legal h.legal_left) htry'))
    (congrArg (fun v => [v]) (head_mem_eq_of_step r q qs o h htry'))

private theorem head_try_of_sat (r : List Color) (q : Quantifier) (qs : List Quantifier)
    {a b : List Color} {D : Diagram Gate a b} (o : Occurrence (diagram r (q :: qs)) D)
    {u : D.Edge → Bool} (hu : (D.graph Gate.interp).Legal u)
    (hadm : u (o.emb (control r (q :: qs) (q :: qs).length 0)) = false →
      u (o.emb (control r (q :: qs) (q :: qs).length 1)) = true)
    (hsat : u ((o.trans (headOcc r q qs)).emb (q.gadget.bottom 0)) = false) :
    u ((o.trans (headOcc r q qs)).emb (q.gadget.bottom 1)) = true := by
  have htry := try_of_sat qs ([R, R] ++ r) 0 ((o.trans (tailOcc r q qs)).legal hu)
    (by simpa only [List.length_cons, control_cons_succ, Occurrence.emb_trans, Function.comp_def]
      using hadm)
    (by simpa only [control_zero, Function.comp_def] using
      (congrArg u (head_bottom_trans r q qs o 0)).symm.trans hsat)
  exact (congrArg u (head_bottom_trans r q qs o 1)).trans
    (by simpa only [control_zero, Function.comp_def] using htry)

private theorem truth_cons (r : List Color) (q : Quantifier) (qs : List Quantifier)
    {a b : List Color} {D : Diagram Gate a b} (o : Occurrence (diagram r (q :: qs)) D)
    (context : (D.Edge → Bool) → List Bool) (matrix : List Bool → Prop) {s t : D.Edge → Bool}
    (hs : (D.graph Gate.interp).Legal s) (hstart : s (o.emb (input r (q :: qs) 1)) = false)
    (hadm : ∀ u, (D.graph Gate.interp).Reachable s u →
      u (o.emb (control r (q :: qs) (q :: qs).length 0)) = false →
        u (o.emb (control r (q :: qs) (q :: qs).length 1)) = true)
    (hfreeze : ∀ u v, (D.graph Gate.interp).Reachable s u → (D.graph Gate.interp).Step u v →
      u (o.emb (input r (q :: qs) 1)) = true → context u = context v)
    (htail : ∀ u, (D.graph Gate.interp).Reachable s u →
      u ((o.trans (tailOcc r q qs)).emb (input ([R, R] ++ r) qs 0)) = false →
        Truth matrix qs (context u ++ [u (o.emb ((headOcc r q qs).emb q.mem))]))
    (h : (D.graph Gate.interp).Reachable s t) (hsat : t (o.emb (input r (q :: qs) 0)) = false) :
    Truth matrix (q :: qs) (context t) := by
  cases q
  · refine ⟨_, htail t h ?_⟩
    simpa only [Occurrence.emb_trans, Function.comp_def] using
      first_sat r .ex qs (o.legal (h.legal hs)) hsat
  · refine ForallGadget.forall_of_reachable (o.trans (headOcc r .all qs)) context
      (fun values value => Truth matrix qs (values ++ [value]))
      (fun u hu => head_try_of_sat r .all qs o (hu.legal hs) (hadm u hu))
      (fun u v hu huv htry => hfreeze u v hu huv
        ((congrArg u (head_top_trans r .all qs o 1)).symm.trans htry))
      (fun u hu hlocal => ?_) hs ((congrArg s (head_top_trans r .all qs o 1)).trans hstart) h
      ((congrArg t (head_top_trans r .all qs o 0)).trans hsat)
    have hm := congrArg u (congrFun (o.emb_trans (headOcc r .all qs)) ForallGadget.mem)
    exact (congrArg (fun value => Truth matrix qs (context u ++ [value])) hm).mpr
      (htail u hu ((congrArg u (head_bottom_trans r .all qs o 0)).symm.trans hlocal))

/-- **Soundness of the whole chain**, relative to its terminal matrix contract. The context
is the current assignment of any preceding variables and need only be frozen while this chain
is tried. Both terminal hypotheses are required only at reachable configurations. -/
theorem truth_of_reachable : ∀ (qs : List Quantifier) (r : List Color)
    {a b : List Color} {D : Diagram Gate a b} (o : Occurrence (diagram r qs) D)
    (context : (D.Edge → Bool) → List Bool) (matrix : List Bool → Prop) {s t : D.Edge → Bool},
    (D.graph Gate.interp).Legal s → s (o.emb (input r qs 1)) = false →
    (∀ u, (D.graph Gate.interp).Reachable s u →
      u (o.emb (control r qs qs.length 0)) = false → u (o.emb (control r qs qs.length 1)) = true) →
    (∀ u v, (D.graph Gate.interp).Reachable s u → (D.graph Gate.interp).Step u v →
      u (o.emb (input r qs 1)) = true → context u = context v) →
    (∀ u, (D.graph Gate.interp).Reachable s u → u (o.emb (control r qs qs.length 0)) = false →
      matrix (context u ++ memories r qs (u ∘ o.emb))) →
    (D.graph Gate.interp).Reachable s t → t (o.emb (input r qs 0)) = false →
    Truth matrix qs (context t)
  | [], _, _, _, _, _, _, _, _, t, _, _, _, _, hm, h, hsat => by
    simpa only [Truth, memories, List.append_nil] using hm t h hsat
  | q :: qs, r, _, _, _, o, context, matrix, _, _, hs, hstart, hadm, hf, hm, h, hsat =>
    truth_cons r q qs o context matrix hs hstart hadm hf (fun u hu hsat' =>
      truth_of_reachable qs ([R, R] ++ r) (o.trans (tailOcc r q qs))
        (fun u => context u ++ [u (o.emb ((headOcc r q qs).emb q.mem))]) matrix hs
        (tail_inactive r q qs o hs hstart)
        (fun v hv => by
          simpa only [List.length_cons, control_cons_succ, Occurrence.emb_trans,
            Function.comp_def] using hadm v hv)
        (fun v w hv hvw => tail_context_eq r q qs o context hvw (hf v w hv hvw))
        (fun v hv hfinal => by
          have hm' := hm v hv (by
            simpa only [List.length_cons, control_cons_succ, Occurrence.emb_trans,
              Function.comp_def] using hfinal)
          simpa only [memories, Occurrence.emb_trans, Function.comp_def, List.append_assoc,
            List.cons_append, List.nil_append] using hm')
        hu hsat') h hsat

end Chain

end Cslib.Complexity.NCL.QBF
