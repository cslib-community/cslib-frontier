/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/
module

-- upstream: candidate
public import CslibFrontier.Algorithms.Lean.SoftHeap.Forest
public import Mathlib.Order.WithBot

/-!
# Heap order and minimum extraction

In the ranked soft heap, each descendant bucket has current key at least that of its root.
The double refill retains the larger of its two representative keys. Both pulls select a
minimum and never decrease the representative key of a remaining child.
-/

public section

namespace Cslib.SoftHeap

variable {α W : Type} [LinearOrder W] {r : ℕ}

/-- An empty root compares above every occupied root. -/
@[expose] def key (w : α → W) (b : Option (Bucket α)) : WithTop W :=
  b.elim ⊤ (fun x => ↑(w x.rep))

namespace Tree

/-- Every nonempty child lies below a nonempty parent with no larger representative key. -/
@[expose] def Ordered (w : α → W) : {r : ℕ} → Tree α r → Prop
  | 0, .leaf _ => True
  | _, .node b cs => ∀ i, key w b ≤ key w (cs i).root ∧ (cs i).Ordered w

private theorem leastChild_min {w : α → W} {cs : Fin 4 → Tree α r} {j : Fin 4} {b : Bucket α}
    (hit : leastChild w cs = some (j, b)) (i : Fin 4) : key w (some b) ≤ key w (cs i).root := by
  cases h : (cs i).root with
  | none => exact le_top
  | some c =>
    let rows := (List.finRange 4).filterMap fun k => (cs k).root.map (k, ·)
    have mem : (i, c) ∈ rows := List.mem_filterMap.mpr ⟨i, List.mem_finRange _, by simp [h]⟩
    change rows.minOn? (fun p => w p.2.rep) = some (j, b) at hit
    have bound := List.apply_minOn_le_of_mem (f := fun p : Fin 4 × Bucket α => w p.2.rep) mem
    rw [List.minOn_eq_of_minOn?_eq_some hit] at bound
    exact WithTop.coe_le_coe.mpr bound

private theorem empty_of_leastChild {w : α → W} {cs : Fin 4 → Tree α r}
    (h : leastChild w cs = none) (i : Fin 4) : (cs i).root = none := by
  cases e : (cs i).root with
  | none => rfl
  | some b =>
    have mem : (i, b) ∈ (List.finRange 4).filterMap (fun j => (cs j).root.map (j, ·)) :=
      List.mem_filterMap.mpr ⟨i, List.mem_finRange _, by simp [e]⟩
    have yes : (leastChild w cs).isSome := List.isSome_minOn?_of_mem mem
    simp [h] at yes

private theorem pull_order {w : α → W} {cs : Fin 4 → Tree α r} (next : Tree α r → Tree α r)
    (ih : ∀ tr, tr.Ordered w →
      (next tr).Ordered w ∧ key w tr.root ≤ key w (next tr).root)
    (oc : ∀ i, (cs i).Ordered w) :
    (∀ i, key w (pull w next cs).1 ≤ key w ((pull w next cs).2 i).root ∧
      ((pull w next cs).2 i).Ordered w) ∧
    ∀ z : WithTop W, (∀ i, z ≤ key w (cs i).root) → z ≤ key w (pull w next cs).1 := by
  unfold pull
  cases h : leastChild w cs with
  | none =>
    exact ⟨fun i => ⟨by simp [empty_of_leastChild h i], oc i⟩, fun _ _ => le_top⟩
  | some p =>
    obtain ⟨j, b⟩ := p
    have hb := root_of_leastChild h
    constructor
    · intro i
      by_cases eq : i = j
      · subst i
        simpa only [Function.update_self, hb] using (ih _ (oc j)).symm
      · simpa only [Function.update_of_ne eq] using And.intro (leastChild_min h i) (oc i)
    · intro z hz
      simpa only [hb] using hz j

theorem refill_order (w : α → W) (t : ℕ) (soft : Bool) (tr : Tree α r) (o : tr.Ordered w) :
    (refill w t soft tr).Ordered w ∧ key w tr.root ≤ key w (refill w t soft tr).root := by
  induction r with
  | zero => cases tr; exact ⟨trivial, le_top⟩
  | succ r ih =>
    cases tr with
    | node old cs =>
      let next := refill w t soft (r := r)
      generalize ha : pull w next cs = va
      obtain ⟨a, cs'⟩ := va
      have ⟨ordered, raise⟩ := pull_order next ih (fun i => (o i).2)
      rw [ha] at ordered raise
      have lower := raise (key w old) (fun i => (o i).1)
      simp only [refill, show refill w t soft (r := r) = next from rfl, ha]
      split
      · cases a with
        | none => exact ⟨ordered, lower⟩
        | some a =>
          generalize hb : pull w next cs' = vb
          obtain ⟨b, cs''⟩ := vb
          have ⟨order', rise⟩ := pull_order next ih (fun i => (ordered i).2)
          rw [hb] at order' rise
          cases b with
          | none =>
            constructor
            · intro i
              exact ⟨(show key w (some a) ≤ ⊤ from le_top).trans (order' i).1, (order' i).2⟩
            · exact lower
          | some b =>
            have ab := rise (key w (some a)) (fun i => (ordered i).1)
            have le : w a.rep ≤ w b.rep := WithTop.coe_le_coe.mp ab
            have eq : key w (some (Bucket.pool w a b)) = key w (some b) := by
              simp [key, Bucket.pool, le]
            change (∀ i, key w (some (Bucket.pool w a b)) ≤ key w (cs'' i).root ∧
              (cs'' i).Ordered w) ∧ key w old ≤ key w (some (Bucket.pool w a b))
            rw [eq]
            exact ⟨order', lower.trans ab⟩
      · exact ⟨ordered, lower⟩

theorem link_ordered (w : α → W) (t : ℕ) (cs : Fin 4 → Tree α r)
    (ord : ∀ i, (cs i).Ordered w) : (link w t cs).Ordered w := by
  let seed := (leastChild w cs).map Prod.snd
  have ok : (Tree.node seed cs).Ordered w := by
    intro i
    refine ⟨?_, ord i⟩
    cases h : leastChild w cs with
    | none => simp [seed, h, empty_of_leastChild h i]
    | some p => obtain ⟨j, b⟩ := p; simpa [seed, h] using leastChild_min h i
  exact (refill_order w t false (.node seed cs) ok).1

theorem extract_order {w : α → W} {t : ℕ} {tr tr' : Tree α r} {x a : α} (o : tr.Ordered w)
    (hit : extract w t tr = some ((x, a), tr')) :
    tr'.Ordered w ∧ key w tr.root = ↑(w a) := by
  unfold extract at hit
  split at hit
  · contradiction
  · next b e =>
      cases hit
      exact ⟨(refill_order w t true tr o).1, by rw [e]; rfl⟩
  · next b y ys e =>
      cases hit
      refine ⟨?_, by rw [e]; rfl⟩
      cases tr with
      | leaf => trivial
      | node old cs =>
        intro i
        exact ⟨by simpa only [key, Option.elim_some] using Eq.subst (motive := fun z =>
            key w z ≤ key w (cs i).root) e (o i).1, (o i).2⟩

end Tree
end Cslib.SoftHeap
