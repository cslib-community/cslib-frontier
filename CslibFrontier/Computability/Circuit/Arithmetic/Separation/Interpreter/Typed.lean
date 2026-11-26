/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Interpreter.Lists
public import CslibFrontier.Foundations.Data.List.Weighted
import CslibFrontier.Foundations.Data.List.Blocks
import Mathlib.Algebra.BigOperators.Ring.List

/-!
# Programs whose values are encodings of typed values

The values of a formula of the tree machine are trees. A program that computes with states of a
type `β` holds a state `b` as its encoding `enc b : Tree`, and its weighted list of values is
`l.map (Prod.map id enc)` for a weighted list `l : List (A × β)` of typed values. This file has
the rules of `Interpreter.Does` for such lists: the second part of a sequence is given at every
typed value `b`, and the list of the sequence is `l.weightedBind f` (`List.weightedBind`). The
encoding need not be injective.

The operations `Interpreter.wsum`, `Interpreter.bindW`, `Interpreter.foldW` of the interpreter are
the operations `List.weightedSum`, `List.weightedBind`, `List.weightedFoldl` of weighted lists at
the type of trees.

## Main results

* `Interpreter.wsum_eq_weightedSum`, `Interpreter.bindW_eq_weightedBind`,
  `Interpreter.foldW_eq_weightedFoldl`.
* `Interpreter.Does.wsum_unique`: the weighted sums are determined by the program.
* `Interpreter.Does.of_eq`: replace the list by an equal one.
* `Interpreter.Does.app_enc`, `Does.lett_enc`, `Does.lett_enc_enc`, `Does.letk_enc`,
  `Does.run_enc`: sequences with typed values in the middle.
* `Interpreter.Does.ite_nil`: a condition with the empty value and a weight.
* `Interpreter.foldF_does_enc`, `Interpreter.foldF_gives_enc`: folds with a typed state over a
  list of typed elements.

## References

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], Appendix J.3 (the evaluator in the proof of
Theorem J.3); module `Nc.Grp.Lang`.
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Interpreter

open Cslib.Circuits.Arithmetic.Separation.Interpreter.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A} {β γ ε : Type*}

theorem wsum_eq_weightedSum (Q : List (A × Tree)) (φ : Tree → A) :
    wsum Q φ = Q.weightedSum φ := rfl

theorem bindW_eq_weightedBind (Q : List (A × Tree)) (R : Tree → List (A × Tree)) :
    bindW Q R = Q.weightedBind R := rfl

theorem foldW_eq_weightedFoldl (f : Tree → Tree → List (A × Tree)) (xs : List Tree) (σ : Tree) :
    foldW f xs σ = xs.weightedFoldl f σ := by
  induction xs generalizing σ with
  | nil => rfl
  | cons x xs ih => exact congrArg (bindW (f x σ)) (funext ih)

namespace Does

variable {F G H : Fm} {x : Tree} {Q Q' : List (A × Tree)} {l : List (A × β)} {enc : β → Tree}
  {f : β → List (A × Tree)} {c d : ℕ}

/-- The weighted sums are determined by the program. -/
theorem wsum_unique (h : Does θ F x Q c) (h' : Does θ F x Q' d) (φ : Tree → A) :
    wsum Q φ = wsum Q' φ := by
  rw [← h.evl.2 φ, ← h'.evl.2 φ]

/-- Replace the list by an equal one. -/
theorem of_eq (h : Does θ F x Q c) (hQ : Q = Q') : Does θ F x Q' c := hQ ▸ h

/-- A rule that runs a program `P` at every value of a weighted list (as `Does.app` and
`Does.runW` do), for a list of encodings of typed values: the list `f b` of the program at `enc b`
may depend on `b` and not only on `enc b`. -/
private theorem bind_enc {P : Fm}
    (hP : ∀ b ∈ l, Does θ P (enc b.2) (f b.2) d)
    (rule : ∀ R : Tree → List (A × Tree),
      (∀ q ∈ l.map (Prod.map id enc), Does θ P q.2 (R q.2) d) →
        Does θ F x (bindW (l.map (Prod.map id enc)) R) c) :
    Does θ F x (l.weightedBind f) c := by
  let R : Tree → List (A × Tree) := fun t =>
    ((l.find? fun b => enc b.2 = t).map fun b => f b.2).getD []
  have hR : ∀ b ∈ l, ∃ b' ∈ l, R (enc b.2) = f b'.2 ∧ enc b'.2 = enc b.2 := fun b hb => by
    cases h : l.find? fun b' => enc b'.2 = enc b.2 with
    | none => simpa using List.find?_eq_none.1 h b hb
    | some b' =>
      exact ⟨b', List.mem_of_find?_eq_some h, by simp [R, h], by simpa using List.find?_some h⟩
  refine (rule R fun q hq => ?_).congr (fun q hq => ?_) fun φ => ?_
  · obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hq
    obtain ⟨b', hb', e1, e2⟩ := hR b hb
    rw [Prod.map_snd, e1, ← e2]
    exact hP b' hb'
  · obtain ⟨a, ha, r, hr, rfl⟩ := List.mem_weightedBind_iff.1 hq
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ha
    obtain ⟨b', hb', e1, -⟩ := hR b hb
    exact ⟨_, List.mem_weightedBind_iff.2 ⟨b', hb', r, e1 ▸ hr, rfl⟩, rfl⟩
  · rw [wsum_bindW, wsum_eq_weightedSum, wsum_eq_weightedSum, List.weightedSum_weightedBind,
      List.weightedSum_map]
    refine List.weightedSum_congr fun b hb => ?_
    obtain ⟨b', hb', e1, e2⟩ := hR b hb
    exact e1 ▸ (e2 ▸ hP b' hb').wsum_unique (hP b hb) φ

/-- Apply a fixed program to typed values. -/
theorem app_enc {p : Tree} (hF : Does θ F x (l.map (Prod.map id enc)) c)
    (hG : ∀ b ∈ l, Does θ (Fm.ofTree p) (enc b.2) (f b.2) d) :
    Does θ (Interpreter.app p F) x (l.weightedBind f) (c + d + 2) :=
  bind_enc hG fun _ => hF.app

/-- Apply a program that is the value of a formula to typed values. -/
theorem run_enc {p : Tree} {e : ℕ} (hF : Gives θ F x p c)
    (hG : Does θ G x (l.map (Prod.map id enc)) d)
    (h : ∀ b ∈ l, Does θ (Fm.ofTree p) (enc b.2) (f b.2) e) :
    Does θ (.run F G) x (l.weightedBind f) (c + d + e + 1) :=
  bind_enc h fun _ => runW hF hG

/-- `let` with typed values. -/
theorem lett_enc (hF : Does θ F x (l.map (Prod.map id enc)) c)
    (hG : ∀ b ∈ l, Does θ G (enc b.2) (f b.2) d) :
    Does θ (Interpreter.lett F G) x (l.weightedBind f) (c + d + 2) :=
  app_enc (p := G.code) hF (by rwa [Fm.ofTree_code])

/-- `let` with typed values and typed results. -/
theorem lett_enc_enc {enc' : γ → Tree} {f : β → List (A × γ)}
    (hF : Does θ F x (l.map (Prod.map id enc)) c)
    (hG : ∀ b ∈ l, Does θ G (enc b.2) ((f b.2).map (Prod.map id enc')) d) :
    Does θ (Interpreter.lett F G) x ((l.weightedBind f).map (Prod.map id enc')) (c + d + 2) :=
  List.map_weightedBind l f enc' ▸ lett_enc hF hG

/-- `let`, with the argument kept, typed values. -/
theorem letk_enc (hF : Does θ F x (l.map (Prod.map id enc)) c)
    (hG : ∀ b ∈ l, Does θ G (.cons x (enc b.2)) (f b.2) d) :
    Does θ (Interpreter.lett (.cons .id F) G) x (l.weightedBind f) (c + d + 4) := by
  have h1 : Does θ (.cons .id F) x (l.map (Prod.map id fun b => .cons x (enc b))) (1 + c + 1) :=
    (Does.cons (Gives.id x) hF).of_eq (by simp [Prod.map])
  exact (lett_enc h1 hG).mono (by omega)

/-- The first of two formulas has the empty value, with a weight: go on with the last one. -/
theorem ite_nil {a : A} (hF : Does θ F x [(a, .nil)] c) (hH : Does θ H x Q d) :
    Does θ (.ite F G H) x (Q.map fun r => (a * r.1, r.2)) (c + d + 1) := by
  obtain ⟨l, e1, e2, e3⟩ := hF
  obtain ⟨l', f1, f2, f3⟩ := hH
  have hout : ∀ r ∈ l, r.out = .nil := fun r hr => by
    obtain ⟨-, -, q, hq, h⟩ := e2 r hr
    exact h.symm.trans (congrArg Prod.snd (List.mem_singleton.1 hq))
  refine ⟨_, Ev.ite (L := fun _ => l') e1 (fun r hr h => absurd (hout r hr) h) fun _ _ _ => f1,
    fun u hu => ?_, fun φ => ?_⟩
  · simp only [List.mem_flatMap, List.mem_map] at hu
    obtain ⟨r, hr, s, hs, rfl⟩ := hu
    obtain ⟨a1, a2, -⟩ := e2 r hr
    obtain ⟨b1, b2, q, hq, b3⟩ := f2 s hs
    refine ⟨by simp [Run.seq, Run.tick, a1, b1], ?_, _, List.mem_map.2 ⟨q, hq, rfl⟩, b3⟩
    simp only [Run.seq, Run.tick]
    omega
  · have h1 : ∀ r ∈ l, ((l'.map fun s => (r.seq s).tick s.out).map fun u => u.th * φ u.out).sum =
        r.th * wsum Q φ := fun r _ => by
      rw [List.map_map, ← f3 φ, ← List.sum_map_mul_left]
      exact congrArg List.sum (List.map_congr_left fun t _ => by
        simp only [Function.comp_apply, Run.seq, Run.tick, mul_assoc])
    rw [List.sum_map_flatMap, List.map_congr_left h1, e3 fun _ => wsum Q φ, wsum_cons, wsum_nil,
      add_zero]
    exact (List.weightedSum_map_mul_left a Q φ).symm

end Does

section Fold

variable {encE : ε → Tree} {enc : β → Tree} {Inv : List ε → β → Prop} {d : ε → ℕ} {xs : List ε}

/-- The body of a fold, with a typed state and typed elements. -/
private theorem foldB_does_enc {step : Fm} {f : ε → β → List (A × β)}
    (h : ∀ x ys s, x ∈ xs → Inv (x :: ys) s →
      Does θ step (.cons (encE x) (enc s)) ((f x s).map (Prod.map id enc)) (d x) ∧
        ∀ q ∈ f x s, Inv ys q.2)
    {s : β} (hs : Inv xs s) :
    Does θ (foldB step) (.cons (foldB step).code (.cons (enc s) (listT (xs.map encE))))
      ((xs.weightedFoldl f s).map (Prod.map id enc)) ((xs.map fun x => d x + 30).sum + 10) := by
  induction xs generalizing s with
  | nil => exact (Does.ite_false (Gives.id _).tl.tl (Gives.id _).tl.hd).mono (by simp)
  | cons x xs ih =>
    obtain ⟨h1, h2⟩ := h x xs s List.mem_cons_self hs
    set X : Tree := .cons (foldB step).code (.cons (enc s) (listT ((x :: xs).map encE)))
    have hX : Gives θ .id X X 1 := Gives.id X
    -- the new state, as the argument of the next call
    have e1 : Does θ (.cons (.hd .id) (.cons
        (lett (.cons (.hd (.tl (.tl .id))) (.hd (.tl .id))) step) (.tl (.tl (.tl .id))))) X
        ((f x s).map (Prod.map id fun s' =>
          .cons (foldB step).code (.cons (enc s') (listT (xs.map encE))))) _ :=
      (Does.cons hX.hd (Does.cons (Does.of_gives (hX.tl.tl.hd.cons hX.tl.hd) h1)
        hX.tl.tl.tl)).of_eq (by
          simp [X, listT, ← List.map_eq_flatMap, Function.comp_def, Prod.map])
    -- the next call
    have e2 := Does.run_enc (p := (foldB step).code)
      (f := fun s' => (xs.weightedFoldl f s').map (Prod.map id enc)) hX.hd e1 fun b hb => by
        rw [Fm.ofTree_code]
        exact ih (fun y ys s hy => h y ys s (List.mem_cons_of_mem _ hy)) (h2 b hb)
    rw [← List.map_weightedBind] at e2
    refine (Does.ite_true hX.tl.tl (by simp [X, listT]) e2).mono ?_
    simp only [List.map_cons, List.sum_cons]
    omega

/-- A fold with a typed state over a list of typed elements. -/
theorem foldF_does_enc {step s l : Fm} {x : Tree} {f : ε → β → List (A × β)} {cs cl : ℕ} {s₀ : β}
    (hs : Gives θ s x (enc s₀) cs) (hl : Gives θ l x (listT (xs.map encE)) cl)
    (h : ∀ x ys s, x ∈ xs → Inv (x :: ys) s →
      Does θ step (.cons (encE x) (enc s)) ((f x s).map (Prod.map id enc)) (d x) ∧
        ∀ q ∈ f x s, Inv ys q.2)
    (h0 : Inv xs s₀) :
    Does θ (foldF step s l) x ((xs.weightedFoldl f s₀).map (Prod.map id enc))
      (cs + cl + (xs.map fun x => d x + 30).sum + 20) :=
  (Does.of_gives ((Gives.quote (foldB step).code x).cons (hs.cons hl))
    (foldB_does_enc h h0)).mono (by omega)

/-- A deterministic fold with a typed state over a list of typed elements. -/
theorem foldF_gives_enc {step s l : Fm} {x : Tree} {g : ε → β → β} {cs cl : ℕ} {s₀ : β}
    (hs : Gives θ s x (enc s₀) cs) (hl : Gives θ l x (listT (xs.map encE)) cl)
    (h : ∀ x ys s, x ∈ xs → Inv (x :: ys) s →
      Gives θ step (.cons (encE x) (enc s)) (enc (g x s)) (d x) ∧ Inv ys (g x s))
    (h0 : Inv xs s₀) :
    Gives θ (foldF step s l) x (enc (xs.foldl (fun s x => g x s) s₀))
      (cs + cl + (xs.map fun x => d x + 30).sum + 20) := by
  have := foldF_does_enc (f := fun x s => [((1 : A), g x s)]) hs hl (fun x ys s hx hs =>
    ⟨(h x ys s hx hs).1, fun q hq => List.mem_singleton.1 hq ▸ (h x ys s hx hs).2⟩) h0
  rwa [List.weightedFoldl_singleton_one] at this

end Fold

end Cslib.Circuits.Arithmetic.Separation.Interpreter
