/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Interpreter.Lists
import Mathlib.Tactic.Ring

/-!
# Programs on lists with constantly many entries

Programs of the tree machine for lists whose length is a constant of the program, with their
values (`Interpreter.Gives`, `Interpreter.Does`): the entry at a fixed position, the list of the
values of fixed formulas, a constant word pushed on a list, and case distinctions by fixed
numbers of bits and by a number below a constant.

## Main definitions

* `Interpreter.nthF`: the entry at position `k` of a list.
* `Interpreter.listF`: the list of the values of a list of formulas.
* `Interpreter.pushF`: push a constant word on a list.
* `Interpreter.dispF`: distinguish the values of `m` bits.
* `Interpreter.switchF`: distinguish the values of a number.

## Main results

* `Interpreter.nthF_gives`, `Interpreter.nthF_gives_ofFn`, `Interpreter.listF_gives`,
  `Interpreter.pushF_gives`, `Interpreter.dispF_does`, `Interpreter.switchF_does`: the values of
  these programs.
* `Interpreter.hd_listT`, `Interpreter.tl_listT`, `Interpreter.Tree.hd_ofBits`,
  `Interpreter.Tree.tl_ofBits`: first entries and rests of lists as trees.
* `Interpreter.num_eq_listT_replicate`, `Interpreter.Tree.num_eq_ofBits_replicate`: a number is
  a list of empty trees, and a word of zeros.

## References

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], Appendix J.3 (the evaluator in the proof of
Theorem J.3); module `Nc.Grp.Trans`.
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Interpreter

open Cslib.Circuits.Arithmetic.Separation.Interpreter.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A}

theorem hd_listT (l : List Tree) : (listT l).hd = l.getD 0 .nil := by cases l <;> rfl

theorem tl_listT (l : List Tree) : (listT l).tl = listT l.tail := by cases l <;> rfl

theorem Tree.hd_ofBits (w : List Bool) : (ofBits w).hd = bit (w.headD false) := by
  cases w <;> rfl

theorem Tree.tl_ofBits (w : List Bool) : (ofBits w).tl = ofBits w.tail := by cases w <;> rfl

theorem num_eq_listT_replicate (k : ℕ) : num k = listT (List.replicate k .nil) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [num, ih, List.replicate_succ, listT]

theorem Tree.num_eq_ofBits_replicate (k : ℕ) : num k = ofBits (List.replicate k false) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [num, ih, List.replicate_succ, ofBits]; rfl

/-- The entry at position `k` of the list that `b` gives. -/
@[expose] def nthF : ℕ → Fm → Fm
  | 0, b => .hd b
  | k + 1, b => nthF k (.tl b)

theorem nthF_gives {b : Fm} {x : Tree} {l : List Tree} {c : ℕ} (k : ℕ)
    (h : Gives θ b x (listT l) c) : Gives θ (nthF k b) x (l.getD k .nil) (c + k + 1) := by
  induction k generalizing b l c with
  | zero => exact hd_listT l ▸ h.hd
  | succ k ih =>
    have e : l.tail.getD k (.nil : Tree) = l.getD (k + 1) .nil := by cases l <;> simp
    exact e ▸ (ih (tl_listT l ▸ h.tl)).mono (by omega)

/-- An entry of a list that is given by its entries. -/
theorem nthF_gives_ofFn {b : Fm} {x : Tree} {m c : ℕ} {o : Fin m → Tree} (i : Fin m)
    (h : Gives θ b x (listT (List.ofFn o)) c) : Gives θ (nthF i b) x (o i) (c + m) := by
  have e : (List.ofFn o).getD i .nil = o i := by simp
  exact e ▸ (nthF_gives i h).mono (by omega)

/-- The list of the values of the formulas of a list. -/
@[expose] def listF : List Fm → Fm
  | [] => .quote .nil
  | f :: fs => .cons f (listF fs)

theorem listF_gives {m : ℕ} {f : Fin m → Fm} {x : Tree} {o : Fin m → Tree} {c : ℕ}
    (h : ∀ i, Gives θ (f i) x (o i) c) :
    Gives θ (listF (List.ofFn f)) x (listT (List.ofFn o)) (m * (c + 1) + 1) := by
  induction m with
  | zero => simpa [listF, listT] using Gives.quote (θ := θ) .nil x
  | succ m ih =>
    rw [List.ofFn_succ, List.ofFn_succ]
    exact ((h 0).cons (ih fun i => h i.succ)).mono (by ring_nf; omega)

/-- Push a constant word on the list that `b` gives. -/
@[expose] def pushF : List Tree → Fm → Fm
  | [], b => b
  | t :: ts, b => .cons (.quote t) (pushF ts b)

theorem pushF_gives {b : Fm} {x : Tree} {l : List Tree} {c : ℕ} (ts : List Tree)
    (h : Gives θ b x (listT l) c) :
    Gives θ (pushF ts b) x (listT (ts ++ l)) (c + 2 * ts.length) := by
  induction ts with
  | nil => exact h
  | cons t ts ih => exact ((Gives.quote t x).cons ih).mono (by rw [List.length_cons]; omega)

/-- Distinguish the values of the bits that `g 0, …, g (m - 1)` give: go on with `k v` at the
values `v`. -/
@[expose] def dispF : (m : ℕ) → (Fin m → Fm) → ((Fin m → Bool) → Fm) → Fm
  | 0, _, k => k Fin.elim0
  | m + 1, g, k => .ite (g 0) (dispF m (fun i => g i.succ) fun v => k (Fin.cons true v))
      (dispF m (fun i => g i.succ) fun v => k (Fin.cons false v))

theorem dispF_does {m : ℕ} {g : Fin m → Fm} {k : (Fin m → Bool) → Fm} {x : Tree}
    {v : Fin m → Bool} {Q : List (A × Tree)} {c d : ℕ} (hg : ∀ i, Gives θ (g i) x (bit (v i)) c)
    (hk : Does θ (k v) x Q d) : Does θ (dispF m g k) x Q (m * (c + 1) + d) := by
  induction m with
  | zero => exact (Subsingleton.elim v Fin.elim0 ▸ hk).mono (by omega)
  | succ m ih =>
    have h1 := ih (k := fun w => k (Fin.cons (v 0) w)) (fun i => hg i.succ)
      ((Fin.cons_self_tail v).symm ▸ hk)
    have h0 := hg 0
    cases hb : v 0 <;> rw [hb] at h0 h1
    · exact (Does.ite_false h0 h1).mono (by ring_nf; omega)
    · exact (Does.ite_true h0 (bit_ne_nil.2 rfl) h1).mono (by ring_nf; omega)

/-- Distinguish the values of the number that `t` gives: go on with the formula at that position
of the list, and reject if there is none. -/
@[expose] def switchF (t : Fm) : List Fm → Fm
  | [] => .fail
  | f :: fs => .ite t (switchF (.tl t) fs) f

theorem switchF_does {t : Fm} {fs : List Fm} {x : Tree} {j c d : ℕ} {Q : List (A × Tree)}
    (ht : Gives θ t x (num j) c) {f : Fm} (hf : fs[j]? = some f) (h : Does θ f x Q d) :
    Does θ (switchF t fs) x Q ((j + 1) * (c + j + 1) + d) := by
  induction fs generalizing t j c with
  | nil => simp at hf
  | cons f' fs ih =>
    cases j with
    | zero =>
      obtain rfl : f' = f := by simpa using hf
      exact (Does.ite_false ht h).mono (by omega)
    | succ j =>
      have h1 := ih (c := c + 1) ht.tl (by simpa using hf)
      exact (Does.ite_true ht (by simp [num]) h1).mono (by ring_nf at h1 ⊢; omega)

end Cslib.Circuits.Arithmetic.Separation.Interpreter
