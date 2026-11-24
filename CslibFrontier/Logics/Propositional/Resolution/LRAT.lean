/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CNF.LRAT
public import CslibFrontier.Logics.Propositional.Resolution.TreeLike

/-! # LRAT certificates from tree-like resolution refutations

A resolvent is a RUP clause of its two premises: from the negation of `c₁.resolvent c₂ v`, every
literal of `c₁` but `(v, true)` is false, so `c₁` forces `v`, and then every literal of `c₂` is
false. So a tree-like derivation (`Cslib.Logic.PL.CNF.Derivation`) compiles to an LRAT
certificate with one RUP step for each resolution step, hinting the numbers of its two premises,
followed by an empty-clause step hinting the conclusion, for a derivation of the empty clause
(`Cslib.Logic.PL.CNF.Derivation.toLRAT`). The checker accepts the certificate of every tree-like
refutation (`Cslib.Logic.PL.CNF.Derivation.checkLRAT_toLRAT`).

The clauses of the formula keep their numbers `1, 2, …`; a leaf names the first clause of the
formula equal to it, and the resolvents are numbered from one past the last clause of the formula
on, in post-order.

## Main definitions

* `Cslib.Logic.PL.CNF.Derivation.lratSteps`, `Cslib.Logic.PL.CNF.Derivation.toLRAT`: the
  certificate of a tree-like derivation.

## Main results

* `Cslib.Logic.PL.CNF.Derivation.checkLRAT_toLRAT`: the checker accepts the certificate of a
  tree-like refutation.
* `Cslib.Logic.PL.CNF.Derivation.size_toLRAT`: the certificate of a tree-like refutation has one
  step for each leaf: a RUP step for each resolution step, and the final empty-clause step.
-/

@[expose] public section

namespace Cslib.Logic.PL

open Std.Tactic.BVDecide (LRAT.IntAction)

namespace CNF

variable {φ : CNF ℕ}

/-- The steps of the certificate of a tree-like derivation, the number of its conclusion, and the
next unused number. -/
structure LRATSteps where
  /-- The steps, in order. -/
  actions : List LRAT.IntAction
  /-- The number of the conclusion. -/
  id : ℕ
  /-- The first number not yet used. -/
  next : ℕ

namespace Derivation

/-- The steps of the certificate of a tree-like derivation, numbering its resolvents from `k` on:
nothing for a clause of the formula, and for a resolvent the steps of its premises followed by a
RUP step hinting them. -/
def lratSteps : {c : Clause ℕ} → φ.Derivation c → ℕ → LRATSteps
  | _, mem (c := c) _, k => ⟨[], φ.idxOf c + 1, k⟩
  | _, resolvent (c₁ := c₁) (c₂ := c₂) v d₁ d₂ _ _, k =>
    let r₁ := d₁.lratSteps k
    let r₂ := d₂.lratSteps r₁.next
    ⟨r₁.actions ++ r₂.actions ++ [.addRup r₂.next (c₁.resolvent c₂ v).toDIMACS #[r₁.id, r₂.id]],
      r₂.next, r₂.next + 1⟩

/-- **The LRAT certificate of a tree-like refutation**: its steps, numbering the resolvents from
one past the last clause of the formula, and an empty-clause step hinting its conclusion. -/
def toLRAT (d : φ.Derivation []) : Array LRAT.IntAction :=
  let r := d.lratSteps (φ.length + 1)
  (r.actions ++ [Std.Tactic.BVDecide.LRAT.Action.addEmpty r.next #[r.id]]).toArray


/-- The steps of the certificate of a tree-like derivation: one for each resolution step, so one
fewer than its leaves. -/
private theorem length_actions_lratSteps_add_one : {c : Clause ℕ} → (d : φ.Derivation c) → (k : ℕ) →
    (d.lratSteps k).actions.length + 1 = d.toDecisionTree.leafCount
  | _, mem _, _ => rfl
  | _, resolvent _ d₁ d₂ _ _, k => by
    have h₁ := d₁.length_actions_lratSteps_add_one k
    have h₂ := d₂.length_actions_lratSteps_add_one (d₁.lratSteps k).next
    simp only [lratSteps, toDecisionTree, DecisionTree.leafCount, List.length_append,
      List.length_singleton]
    omega

/-- **The certificate of a tree-like refutation has one step for each of its leaves**: a RUP step
for each resolution step, and the final empty-clause step. -/
theorem size_toLRAT (d : φ.Derivation []) : d.toLRAT.size = d.toDecisionTree.leafCount := by
  simp only [toLRAT, List.size_toArray, List.length_append, List.length_singleton]
  exact d.length_actions_lratSteps_add_one _

end Derivation

/-! ### The checker accepts the certificate -/

/-- Unit propagation from the negation of a resolvent, hinting its two premises, succeeds: the
first premise propagates `v`, and then every literal of the second is false. -/
theorem propagateHints_resolvent {db : List (ℕ × Clause ℕ)} {i₁ i₂ v : ℕ} {c₁ c₂ : Clause ℕ}
    (h₁ : db.find? (·.1 == i₁) = some (i₁, c₁)) (h₂ : db.find? (·.1 == i₂) = some (i₂, c₂)) :
    propagateHints db ((c₁.resolvent c₂ v).map Std.Sat.Literal.negate) [i₁, i₂] = true := by
  have hT : ∀ l ∈ c₁.resolvent c₂ v,
      Std.Sat.Literal.negate l ∈ (c₁.resolvent c₂ v).map Std.Sat.Literal.negate :=
    fun l hl => List.mem_map.2 ⟨l, hl, rfl⟩
  refine propagateHints_cons_of_forall_ne (l := (v, true)) h₁
    (fun m hm hne => hT m (Clause.mem_resolvent.2 (.inl ⟨hm, hne⟩))) fun _ _ => ?_
  exact propagateHints_cons_of_forall_ne (l := (v, false)) h₂
    (fun m hm hne => List.mem_cons_of_mem _ (hT m (Clause.mem_resolvent.2 (.inr ⟨hm, hne⟩))))
    fun _ h => (h (by simp [Std.Sat.Literal.negate])).elim

/-- A database that numbers every clause of the formula as `checkLRAT` does, and every other
entry below `k`. -/
private def LRATGood (φ : CNF ℕ) (k : ℕ) (db : List (ℕ × Clause ℕ)) : Prop :=
  (∀ e ∈ db, e.1 < k) ∧ ∀ c ∈ φ, db.find? (·.1 == φ.idxOf c + 1) = some (φ.idxOf c + 1, c)

/-- The steps of a tree-like derivation pass the checker, adding its conclusion to the database
under its number and keeping the entries below `k`. -/
private theorem Derivation.checkLRATAux_lratSteps {c : Clause ℕ} (d : φ.Derivation c) :
    ∀ (k : ℕ) (db : List (ℕ × Clause ℕ)), φ.length < k → LRATGood φ k db →
      ∃ db', (∀ rest, checkLRATAux db ((d.lratSteps k).actions ++ rest) = checkLRATAux db' rest) ∧
        db'.find? (·.1 == (d.lratSteps k).id) = some ((d.lratSteps k).id, c) ∧
        k ≤ (d.lratSteps k).next ∧ (d.lratSteps k).id < (d.lratSteps k).next ∧
        LRATGood φ (d.lratSteps k).next db' ∧
          ∀ j < k, db'.find? (·.1 == j) = db.find? (·.1 == j) := by
  induction d with
  | @mem c hc =>
    intro k db hk hdb
    have hidx : φ.idxOf c < φ.length := List.idxOf_lt_length_of_mem hc
    exact ⟨db, fun _ => rfl, hdb.2 c hc, le_rfl, by simp [lratSteps]; omega, hdb, fun _ _ => rfl⟩
  | @resolvent c₁ c₂ v d₁ d₂ hv₁ hv₂ ih₁ ih₂ =>
    intro k db hk hdb
    simp only [lratSteps]
    obtain ⟨db₁, hrun₁, hid₁, hk₁, hlt₁, hdb₁, hpres₁⟩ := ih₁ k db hk hdb
    obtain ⟨db₂, hrun₂, hid₂, hk₂, hlt₂, hdb₂, hpres₂⟩ :=
      ih₂ (d₁.lratSteps k).next db₁ (by omega) hdb₁
    generalize d₁.lratSteps k = r₁ at *
    generalize d₂.lratSteps r₁.next = r₂ at *
    have hid₁' : db₂.find? (·.1 == r₁.id) = some (r₁.id, c₁) := (hpres₂ _ hlt₁).trans hid₁
    have hprop := propagateHints_resolvent (v := v) hid₁' hid₂
    -- the new entry has a number above every older one
    have hne : ∀ j < r₂.next, (r₂.next == j) = false := fun j hj => by simp; omega
    refine ⟨(r₂.next, c₁.resolvent c₂ v) :: db₂, fun rest => ?_, ?_, ?_, ?_, ⟨?_, ?_⟩, ?_⟩
    · simp only [List.append_assoc, List.singleton_append]
      rw [hrun₁, hrun₂]
      simp only [checkLRATAux, Clause.ofDIMACS_toDIMACS] at hprop ⊢
      simp [hprop]
    · simp
    · omega
    · omega
    · intro e he
      rcases List.mem_cons.1 he with rfl | he
      · simp
      · have := hdb₂.1 e he; omega
    · intro c hc
      have hidx : φ.idxOf c < φ.length := List.idxOf_lt_length_of_mem hc
      rw [List.find?_cons_of_neg (by simp; omega)]
      exact hdb₂.2 c hc
    · intro j hj
      rw [List.find?_cons_of_neg (by simp; omega), hpres₂ j (by omega), hpres₁ j hj]

/-- The numbering of the clauses of a formula by `checkLRAT`, from `n + 1` on, finds every clause
under the number of its first occurrence. -/
private theorem find?_zipIdx_idxOf {c : Clause ℕ} :
    ∀ (φ : CNF ℕ) (n : ℕ), c ∈ φ →
      ((φ.zipIdx n).map fun e => (e.2 + 1, e.1)).find? (·.1 == φ.idxOf c + n + 1) =
        some (φ.idxOf c + n + 1, c)
  | [], _, h => by simp at h
  | c' :: φ, n, h => by
    by_cases hc : c' = c
    · subst hc
      simp [List.zipIdx_cons]
    · have hmem : c ∈ φ := (List.mem_cons.1 h).resolve_left (Ne.symm hc)
      have := find?_zipIdx_idxOf φ (n + 1) hmem
      simp only [List.zipIdx_cons, List.map_cons, List.find?_cons, List.idxOf_cons_ne _ hc]
        at this ⊢
      rw [show (n + 1 == (φ.idxOf c).succ + n + 1) = false by simp,
        show (φ.idxOf c).succ + n + 1 = φ.idxOf c + (n + 1) + 1 by omega]
      exact this

/-- **The checker accepts the certificate of every tree-like refutation.** -/
theorem Derivation.checkLRAT_toLRAT (d : φ.Derivation []) : φ.checkLRAT d.toLRAT = true := by
  have hgood : LRATGood φ (φ.length + 1) φ.lratDB := by
    refine ⟨fun e he => ?_, fun c hc => by
      have := find?_zipIdx_idxOf φ 0 hc
      simp only [Nat.add_zero] at this
      exact this⟩
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 (show e ∈ φ.zipIdx.map fun e => (e.2 + 1, e.1) from he)
    have := List.snd_lt_add_of_mem_zipIdx hp
    simp only at this ⊢
    omega
  obtain ⟨db, hrun, hid, -, -, -, -⟩ := d.checkLRATAux_lratSteps _ _ (by omega) hgood
  simp only [checkLRAT, toLRAT, List.toList_toArray, hrun, checkLRATAux, propagateHints_cons,
    hid]
  rfl

end CNF

end Cslib.Logic.PL
