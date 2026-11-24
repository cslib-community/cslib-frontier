/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/
module

-- upstream: candidate
public import CslibFrontier.Algorithms.Lean.SoftHeap.Forest
import Mathlib.Tactic.FinCases

/-!
# Amortized node visits in soft-heap refills

The counter follows the calls made by `Tree.refill`. Each occupied bucket carries credits,
and an internal node carries one extra credit while it has an occupied child. Above the
threshold a double pull pays for the visit from two consumed buckets. If there is just one
pull, it empties the last child and releases the extra credit. Below the threshold the credit
returned by a child decreases by one at each level.

This counts visits to ranked nodes. Finding the minimum root of the forest and manipulating
the persistent item lists are separate operations.
-/

public section

namespace Cslib.SoftHeap.Tree

variable {α W A : Type} [LinearOrder W] {r : ℕ}

/-- Cost of the recursive call to a child, with zero cost when there is no child to pull. -/
@[expose] def pullVisits (w : α → W) (cost : Tree α r → ℕ) (cs : Fin 4 → Tree α r) : ℕ :=
  (leastChild w cs).elim 0 (fun p => cost (cs p.1))

/-- Count visits to ranked nodes in the soft heap's actual refill recursion. -/
@[expose] def refillVisits (w : α → W) (t : ℕ) (soft : Bool) : {r : ℕ} → Tree α r → ℕ
  | 0, .leaf _ => 1
  | r + 1, .node _ cs =>
    let cost := refillVisits w t soft (r := r)
    let first := pull w (refill w t soft) cs
    1 + pullVisits w cost cs +
      if soft && decide (t < r + 1) && first.1.isSome then pullVisits w cost first.2 else 0

/-- A linking refill makes at most one recursive call per rank. -/
theorem linking_visits_le (w : α → W) (t : ℕ) (tr : Tree α r) :
    refillVisits w t false tr ≤ r + 1 := by
  induction r with
  | zero => cases tr; rfl
  | succ r ih =>
    cases tr with
    | node b cs =>
      simp only [refillVisits, Bool.false_and, Bool.false_eq_true, ite_false, Nat.add_zero]
      unfold pullVisits
      cases e : leastChild w cs with
      | none => simp
      | some p => exact Nat.add_le_add_left (ih _) 1 |>.trans (by omega)

/-- One unit of credit when a slot is occupied. -/
@[expose] def occupied (s : Option A) : ℕ := if s.isSome then 1 else 0

private theorem occupied_le (s : Option A) : occupied s ≤ 1 := by cases s <;> simp [occupied]

/-- Potential for extraction refills. An occupied bucket stores `t + 3` credits. -/
@[expose] def credits (w : α → W) (t : ℕ) : {r : ℕ} → Tree α r → ℕ
  | 0, .leaf b => occupied b * (t + 3)
  | _, .node b cs => occupied b * (t + 3) + occupied (leastChild w cs) +
      ∑ i, (cs i).credits w t

/-- Credits of descendants and the parent's active-child bit. -/
@[expose] def childCredits (w : α → W) (t : ℕ) : {r : ℕ} → Tree α r → ℕ
  | 0, .leaf _ => 0
  | _, .node _ cs => occupied (leastChild w cs) + ∑ i, (cs i).credits w t

theorem credits_root (w : α → W) (t : ℕ) (tr : Tree α r) :
    credits w t tr = occupied tr.root * (t + 3) + childCredits w t tr := by
  cases tr <;> simp [credits, root, childCredits, Nat.add_assoc]

/-- Credits returned by removing a bucket from a node of rank `r`. -/
private def refund (t r : ℕ) (soft : Bool) : ℕ := if soft then t - r + 2 else t + 3

private def debit (w : α → W) (t : ℕ) (soft : Bool) (tr : Tree α r) : ℕ :=
  if soft then refillVisits w t soft tr else 0

private theorem transfer (w : α → W) (t : ℕ) (soft : Bool) (cs : Fin 4 → Tree α r)
    (ih : ∀ tr : Tree α r, debit w t soft tr + credits w t (refill w t soft tr) + refund t r soft ≤
      (t + 3) + childCredits w t tr) :
    let next := refill w t soft (r := r)
    let got := pull w next cs
    pullVisits w (debit w t soft) cs + (∑ i, credits w t (got.2 i)) +
      occupied got.1 * refund t r soft ≤ ∑ i, credits w t (cs i) := by
  simp only [pull, pullVisits]
  cases h : leastChild w cs with
  | none => simp [occupied]
  | some p =>
    obtain ⟨j, b⟩ := p
    have step := ih (cs j)
    have eq := credits_root w t (cs j)
    rw [root_of_leastChild h] at eq
    change credits w t (cs j) = 1 * (t + 3) + _ at eq
    simp only [Nat.one_mul] at eq
    have sumEq : (∑ i, credits w t (Function.update cs j (refill w t soft (cs j)) i)) =
        credits w t (refill w t soft (cs j)) + ∑ i ∈ Finset.univ.erase j, credits w t (cs i) := by
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ j)]
      simp only [Function.update_self]
      congr 1
      exact Finset.sum_congr rfl fun i hi => by
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
    simp only [Option.elim_some, occupied, Option.isSome_some, ite_true, Nat.one_mul]
    rw [sumEq, ← Finset.add_sum_erase Finset.univ (fun i => credits w t (cs i)) (Finset.mem_univ j)]
    omega

private theorem first_some {w : α → W} {next : Tree α r → Tree α r} {cs : Fin 4 → Tree α r} :
    (pull w next cs).1.isSome = (leastChild w cs).isSome := by
  unfold pull
  cases leastChild w cs with | none => rfl | some p => cases p; rfl

private theorem pull_empty {w : α → W} {next : Tree α r → Tree α r} {cs : Fin 4 → Tree α r}
    (h : (pull w next cs).1 = none) : leastChild w cs = none ∧ (pull w next cs).2 = cs := by
  unfold pull at *
  cases e : leastChild w cs with
  | none => exact ⟨rfl, rfl⟩
  | some p => cases p; simp [e] at h

private theorem refill_credit (w : α → W) (t : ℕ) (soft : Bool) (tr : Tree α r) :
    debit w t soft tr + credits w t (refill w t soft tr) + refund t r soft ≤
      (t + 3) + childCredits w t tr := by
  induction r with
  | zero =>
    cases tr; cases soft <;>
      simp [debit, refillVisits, refill, credits, occupied, refund, childCredits]
    omega
  | succ r ih =>
    cases tr with
    | node old cs =>
      let next := refill w t soft (r := r)
      let work := debit w t soft (r := r)
      have one := transfer w t soft cs ih
      generalize h1 : pull w next cs = result
      obtain ⟨a, cs'⟩ := result
      change pullVisits w work cs + _ + _ ≤ _ at one
      rw [show refill w t soft (r := r) = next from rfl, h1] at one
      have workEq (ds : Fin 4 → Tree α r) :
          pullVisits w work ds = if soft then pullVisits w (refillVisits w t soft) ds else 0 := by
        unfold pullVisits
        cases leastChild w ds <;> cases soft <;> rfl
      simp only [debit, refillVisits, refill, show refill w t soft (r := r) = next from rfl, h1,
        childCredits]
      cases a with
      | none =>
        have nil := pull_empty (show (pull w next cs).1 = none by rw [h1])
        have heq : cs' = cs := by simpa only [h1] using nil.2
        subst cs'
        cases soft <;> simp [nil.1, occupied, pullVisits, credits, refund] <;> omega
      | some a =>
        have someChild := first_some (w := w) (next := next) (cs := cs)
        rw [h1] at someChild
        have active : occupied (leastChild w cs) = 1 := by simp [occupied, someChild.symm]
        have one' : pullVisits w work cs + (∑ i, credits w t (cs' i)) + refund t r soft ≤
            ∑ i, credits w t (cs i) := by simpa [occupied] using one
        rw [active]
        cases soft with
        | false =>
          have zero := workEq cs
          simp only [Bool.false_eq_true, ite_false] at zero
          simp only [Bool.false_and, Bool.false_eq_true, ite_false, credits, refund,
            occupied, Option.isSome_some, ite_true, Nat.one_mul] at one' ⊢
          have upper := occupied_le (leastChild w cs')
          unfold occupied at upper
          omega
        | true =>
          have workOne := workEq cs
          simp only [ite_true, refund] at one' workOne
          by_cases high : t < r + 1
          · generalize h2 : pull w next cs' = second
            obtain ⟨b, cs''⟩ := second
            have two := transfer w t true (r := r) cs' ih
            change pullVisits w work cs' + _ + _ ≤ _ at two
            rw [show refill w t true (r := r) = next from rfl, h2] at two
            simp only [high, decide_true, Option.isSome_some,
              Bool.and_true, ite_true, credits, refund, Nat.sub_eq_zero_of_le
                (show t ≤ r by omega), Nat.sub_eq_zero_of_le high.le, Nat.zero_add, occupied,
              Option.isSome_some, Nat.one_mul] at one' two ⊢
            cases b with
            | none =>
              have nil := pull_empty (show (pull w next cs').1 = none by rw [h2])
              have heq : cs'' = cs' := by simpa only [h2] using nil.2
              subst cs''
              simp only [nil.1, Option.isSome_none, Bool.false_eq_true, ite_false]
              have w2 : pullVisits w (refillVisits w t true) cs' = 0 := by simp [pullVisits, nil.1]
              omega
            | some b =>
              have workTwo := workEq cs'
              simp only [ite_true] at workTwo
              have upper := occupied_le (leastChild w cs'')
              simp only [occupied] at upper
              simp only [Option.isSome_some, ite_true, Nat.one_mul] at two
              omega
          · have upper := occupied_le (leastChild w cs')
            simp only [occupied] at upper
            simp only [high, decide_false, Bool.true_and, Bool.false_and, Bool.false_eq_true,
              ite_false, ite_true, Nat.add_zero, credits, occupied, Option.isSome_some, Nat.one_mul,
              refund]
            omega

end Cslib.SoftHeap.Tree

namespace Cslib.SoftHeap.Tree

variable {α W : Type} [LinearOrder W] {r : ℕ}

/-- Linking increases extraction credits by at most one beyond the four input subtrees. -/
theorem link_credits (w : α → W) (t : ℕ) (cs : Fin 4 → Tree α r) :
    credits w t (link w t cs) ≤ 1 + ∑ i, credits w t (cs i) := by
  have bound := refill_credit w t false (.node none cs)
  simp only [debit, Bool.false_eq_true, ite_false, Nat.zero_add, refund, childCredits] at bound
  have one := occupied_le (leastChild w cs)
  change credits w t (refill w t false (.node none cs)) ≤ _
  omega

/-- Refilling after removing a representative is the only extraction branch that visits
ranked descendant nodes. -/
@[expose] def extractVisits (w : α → W) (t : ℕ) (tr : Tree α r) : ℕ :=
  match tr.root with
  | some ⟨_, []⟩ => refillVisits w t true tr
  | _ => 0

/-- A tree pays for every node visited during a successful extraction from its credits. -/
theorem extract_visits_credits {w : α → W} {t : ℕ} {tr tr' : Tree α r} {x a : α}
    (hit : extract w t tr = some ((x, a), tr')) :
    extractVisits w t tr + credits w t tr' ≤ credits w t tr := by
  unfold extract at hit
  split at hit
  · contradiction
  · next b slot =>
    cases hit
    have cost := refill_credit w t true tr
    simp only [debit, ite_true] at cost
    rw [credits_root w t tr, slot]
    simp only [extractVisits, slot, occupied, Option.isSome_some, ite_true, Nat.one_mul]
    omega
  · next b y ys slot =>
    cases hit
    simp only [extractVisits, slot, Nat.zero_add]
    cases tr with
    | leaf old =>
      change old = _ at slot
      rw [slot]; rfl
    | node old cs =>
      change old = _ at slot
      rw [slot]; rfl

end Cslib.SoftHeap.Tree

namespace Cslib.SoftHeap.Forest

variable {α W : Type} [LinearOrder W] {r : ℕ}

/-- The forest credit includes a linear-in-rank reserve for future equal-rank links. -/
@[expose] def refillCredits (w : α → W) (t : ℕ) (h : Forest α) : ℕ :=
  (h.map fun f => f.2.credits w t + (f.1 + 2)).sum

/-- Sum the actual node visits of the linking refills performed by a carry. -/
@[expose] def carryVisits (w : α → W) (t : ℕ) :
    {r : ℕ} → Tree α r → Forest α → ℕ
  | r, tr, ⟨a, A⟩ :: ⟨b, B⟩ :: ⟨c, C⟩ :: rest =>
      if ha : a = r then
        if hb : b = r then
          if hc : c = r then
            let cs := ![tr, ha ▸ A, hb ▸ B, hc ▸ C]
            Tree.refillVisits w t false (.node none cs) + carryVisits w t (Tree.link w t cs) rest
          else 0
        else 0
      else 0
  | _, _, _ => 0
termination_by _ _ h => h.length

theorem carry_visits_credits (w : α → W) (t : ℕ) (tr : Tree α r) (h : Forest α) :
    carryVisits w t tr h + refillCredits w t (carry w t tr h) ≤
      tr.credits w t + (r + 2) + refillCredits w t h := by
  induction r, tr, h using carry.induct w t with
  | case1 r C rest B A tr ih =>
    rw [carry, carryVisits]
    simp only [dite_true]
    have cap := Tree.linking_visits_le w t (.node none ![tr, A, B, C])
    have changeCredit := Tree.link_credits w t ![tr, A, B, C]
    simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three] at changeCredit
    change _ ≤ 1 + (tr.credits w t + A.credits w t + B.credits w t + C.credits w t) at changeCredit
    simp only [refillCredits, List.map_cons, List.sum_cons] at *
    omega
  | case2 | case3 | case4 | case5 =>
    rw [carry, carryVisits]
    all_goals first | assumption | simp_all [refillCredits]

/-- Each insertion pays at most `t + 5` node-visit credits, including the credit placed on
the new singleton. -/
theorem insert_visits_credits (w : α → W) (t : ℕ) (x : α) (h : Forest α) :
    carryVisits w t (Tree.singleton x) h + refillCredits w t (insert w t x h) ≤
      (t + 5) + refillCredits w t h := by
  simpa only [insert, Tree.singleton, Tree.credits, Tree.occupied, Option.isSome_some,
    ite_true, Nat.one_mul, Nat.zero_add] using
    carry_visits_credits w t (Tree.singleton x) h

/-- Visit count for exactly the ranked tree selected by forest extraction. -/
@[expose] def extractVisits (w : α → W) (t : ℕ) (h : Forest α) : ℕ :=
  (leastRoot w h).elim 0 (fun p => Tree.extractVisits w t (h.get p.1).2)

private theorem set_credits (w : α → W) (t : ℕ) (h : Forest α) (i : Fin h.length)
    (tr : Tree α (h.get i).1) (cost : ℕ) (le : cost + tr.credits w t ≤ (h.get i).2.credits w t) :
    cost + refillCredits w t (h.set i ⟨(h.get i).1, tr⟩) ≤ refillCredits w t h := by
  induction h with
  | nil => exact Fin.elim0 i
  | cons f fs ih =>
    induction i using Fin.cases with
    | zero =>
      change cost + tr.credits w t ≤ f.2.credits w t at le
      change cost + (tr.credits w t + (f.1 + 2) + refillCredits w t fs) ≤
        f.2.credits w t + (f.1 + 2) + refillCredits w t fs
      omega
    | succ j =>
      have small := ih j tr le
      change cost + (f.2.credits w t + (f.1 + 2) +
        refillCredits w t (fs.set j ⟨(fs.get j).1, tr⟩)) ≤
        f.2.credits w t + (f.1 + 2) + refillCredits w t fs
      omega

/-- A successful forest extraction pays every ranked-node visit from the forest credit. -/
theorem extract_visits_credits {w : α → W} {t : ℕ} {h h' : Forest α} {x a : α}
    (hit : extract w t h = some ((x, a), h')) :
    extractVisits w t h + refillCredits w t h' ≤ refillCredits w t h := by
  unfold extract at hit
  cases found : leastRoot w h with
  | none => simp [found] at hit
  | some p =>
    obtain ⟨i, b⟩ := p
    cases ran : Tree.extract w t (h.get i).2 with
    | none => simp only [found, Option.bind_some, Option.bind_eq_bind, ran, Option.bind_none,
        Option.pure_def, reduceCtorEq] at hit
    | some result =>
      obtain ⟨⟨y, k⟩, tr⟩ := result
      simp only [found, Option.bind_some, Option.bind_eq_bind, ran, Option.pure_def,
        Option.some.injEq, Prod.mk.injEq] at hit
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hit
      simp only [extractVisits, found, Option.elim_some]
      exact set_credits w t h i tr _ (Tree.extract_visits_credits ran)

/-- Operation histories starting from the empty forest. The two indices count insertions
and the ranked-node visits actually performed by their links and by all extractions. -/
inductive History (w : α → W) (t : ℕ) : Forest α → ℕ → ℕ → Prop
  | empty : History w t [] 0 0
  | insert {h n v} (prior : History w t h n v) (x : α) :
      History w t (Forest.insert w t x h) (n + 1) (v + carryVisits w t (Tree.singleton x) h)
  | extract {h h' n v x a} (prior : History w t h n v)
      (out : Forest.extract w t h = some ((x, a), h')) :
      History w t h' n (v + extractVisits w t h)

/-- Over any successful operation history, the actual refill recursion visits at most
`(threshold + 5) * insertions` ranked nodes. In particular threshold two gives seven visits
per insertion in aggregate. -/
theorem History.refillVisits_le {w : α → W} {t n v : ℕ} {h : Forest α} (hist : History w t h n v) :
    v + refillCredits w t h ≤ (t + 5) * n := by
  induction hist with
  | empty => simp [refillCredits]
  | @insert h n v _ x ih =>
    have pay := insert_visits_credits w t x h
    rw [Nat.mul_succ]
    omega
  | extract _ hit ih =>
    have pay := extract_visits_credits hit
    omega

end Cslib.SoftHeap.Forest
