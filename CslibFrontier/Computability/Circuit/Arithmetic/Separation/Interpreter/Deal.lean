/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Interpreter.Util
import Mathlib.Tactic.Ring

/-!
# Assignments and guessed bit lists

A state is a trie that represents values at paths (`Interpreter.RepW`). An assignment writes a
list of (path, value) pairs into the state (`Interpreter.assignF`). `Interpreter.bitsF` guesses a
bit list of a given length, with all lists of that length (`Interpreter.allBits`) as its values.

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], module `NS1.Deal`.

## Main definitions

* `Interpreter.RepW`, `Interpreter.assignT`, `Interpreter.assignS`, `Interpreter.assignF`.
* `Interpreter.bitsB`, `Interpreter.bitsF`.

## Main results

* `Interpreter.assignF_gives`, `Interpreter.bitsF_does`.
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Interpreter

open Cslib.Circuits.Arithmetic.Separation.Interpreter.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A}

section Assign

/-- The trie `W` has the values `σ`. -/
@[expose] def RepW (W : Tree) (σ : List Bool → Tree) : Prop := ∀ p, tget p W = σ p

theorem RepW.set {W : Tree} {σ : List Bool → Tree} (h : RepW W σ) (p : List Bool) (v : Tree) :
    RepW (tset p v W) (Function.update σ p v) := by
  intro q
  rw [tget_tset, Function.update_apply, h q]

/-- Assign: the elements of the list are pairs (path, value). -/
@[expose] def assignT (W : Tree) (o : Tree) : Tree :=
    o.toList.foldl (fun W x => tset x.hd.path x.tl W) W

/-- Assign, for values. -/
@[expose] def assignS (σ : List Bool → Tree) (o : Tree) : List Bool → Tree :=
  o.toList.foldl (fun σ x => Function.update σ x.hd.path x.tl) σ

theorem RepW.assign {W : Tree} {σ : List Bool → Tree} (h : RepW W σ)
    (o : Tree) : RepW (assignT W o) (assignS σ o) := by
  unfold assignT assignS
  generalize o.toList = l
  induction l generalizing W σ with
  | nil => exact h
  | cons x l ih => exact ih (h.set _ _)

/-- Assign; `o` gives the list, `w` the trie. -/
@[expose] def assignF (o w : Fm) : Fm := foldF (setF (.hd (.hd .id)) (.tl (.hd .id)) (.tl .id)) w o

theorem assignF_gives {of wf : Fm} {x o W : Tree} {co cw : ℕ} (ho : Gives θ of x o co)
    (hw : Gives θ wf x W cw) :
    Gives θ (assignF of wf) x (assignT W o)
        (co + cw + (o.toList.map fun y => 60 * y.hd.len + 80).sum + 20) := by
  have ho' : Gives θ of x (listT o.toList) co := by rw [listT_toList]; exact ho
  have := foldF_gives (step := setF (.hd (.hd .id)) (.tl (.hd .id)) (.tl .id))
      (g := fun y W => tset y.hd.path y.tl W)
    (Inv := fun _ _ => True) (d := fun y => 60 * y.hd.len + 50) hw ho' (fun y _ W _ _ =>
      ⟨(setF_gives (Gives.id _).hd.hd (Gives.id _).hd.tl (Gives.id _).tl).mono
          (by simp only [hd_cons]; omega), trivial⟩)
    trivial
  refine this.mono ?_
  have e : (o.toList.map fun y => 60 * y.hd.len + 50 + 30).sum =
      (o.toList.map fun y => 60 * y.hd.len + 80).sum := by
    congr 1
  omega

end Assign

section Bits

/-- Guess a bit list. The argument is (this program, (length in binary, bits so far)). -/
@[expose] def bitsB : Fm := .ite (app nzB.code (.cons (.quote nzB.code) (.hd (.tl .id))))
  (.ite .guess
    (.run (.hd .id) (.cons (.hd .id) (.cons (app DW.code (.cons (.quote DW.code) (.hd (.tl .id))))
      (.cons (.quote one) (.tl (.tl .id))))))
    (.run (.hd .id) (.cons (.hd .id) (.cons (app DW.code (.cons (.quote DW.code) (.hd (.tl .id))))
      (.cons (.quote .nil) (.tl (.tl .id)))))))
  (.tl (.tl .id))

/-- The test of `bitsB`: whether the remaining length is nonzero. -/
private theorem bitsB_nz (w acc : List Bool) :
    Gives θ (app nzB.code (.cons (.quote nzB.code) (.hd (.tl .id))))
      (.cons bitsB.code (.cons (ofBits w) (ofBits acc))) (bit (decide (KT.val w ≠ 0)))
      (1 + (1 + 1 + 1) + 1 + (20 * w.length + 10) + 2) :=
  Gives.app (Gives.cons (Gives.quote (θ := θ) _ _) (Gives.id (θ := θ) _).tl.hd)
    (by rw [Fm.ofTree_code]; exact nzB_gives (θ := θ) w)

theorem bitsB_does (n : ℕ) : ∀ (w : List Bool) (acc : List Bool), KT.val w = n →
    ∃ Q, Does θ bitsB (.cons bitsB.code (.cons (ofBits w) (ofBits acc))) Q
        ((n + 1) * (60 * w.length + 100)) ∧
      (∀ q ∈ Q, ∃ u ∈ allBits n, q.2 = ofBits (u.reverse ++ acc)) ∧
      ∀ φ : Tree → A, wsum Q φ = ((allBits n).map fun u => φ (ofBits (u.reverse ++ acc))).sum := by
  induction n with
  | zero =>
    intro w acc hw
    have hnz := bitsB_nz (θ := θ) w acc
    have e : bit (decide (KT.val w ≠ 0)) = .nil := by simp [hw, bit]
    rw [e] at hnz
    refine ⟨_, (Does.ite_false hnz (Gives.id _).tl.tl).mono (by omega), ?_, ?_⟩
    · intro q hq
      rw [List.mem_singleton] at hq
      subst hq
      exact ⟨[], by simp [allBits], rfl⟩
    · intro φ
      simp [allBits]
  | succ n ih =>
    intro w acc hw
    have hnz := bitsB_nz (θ := θ) w acc
    have e : bit (decide (KT.val w ≠ 0)) ≠ .nil := by
      have : KT.val w ≠ 0 := by omega
      simp [this, bit, one]
    rcases decw_val w with ⟨h1, h2⟩ | ⟨w', h1, h2⟩
    · omega
    obtain ⟨k, hk, hdw⟩ := DW_some (θ := θ) h1
    have hd : Gives θ (app DW.code (.cons (.quote DW.code) (.hd (.tl .id))))
        (.cons bitsB.code (.cons (ofBits w) (ofBits acc))) (ofBits w')
            (1 + 3 + 1 + 20 * w.length + 2) :=
      Gives.app (p := DW.code) (Gives.cons (Gives.quote DW.code _) (Gives.id _).tl.hd) (by
        rw [Fm.ofTree_code]
        exact (Does.of_dt hdw).mono hk)
    have hl : w'.length = w.length := length_decw h1
    obtain ⟨Q1, d1, q1, v1⟩ := ih w' (true :: acc) (by omega)
    obtain ⟨Q0, d0, q0, v0⟩ := ih w' (false :: acc) (by omega)
    have d1' : Does θ (Fm.ofTree bitsB.code)
        (.cons bitsB.code (.cons (ofBits w') (.cons one (ofBits acc)))) Q1
        ((n + 1) * (60 * w.length + 100)) := by rw [Fm.ofTree_code, ← hl]; exact d1
    have d0' : Does θ (Fm.ofTree bitsB.code)
        (.cons bitsB.code (.cons (ofBits w') (.cons .nil (ofBits acc)))) Q0
        ((n + 1) * (60 * w.length + 100)) := by rw [Fm.ofTree_code, ← hl]; exact d0
    have r1 := Does.run (Gives.id (θ := θ) (.cons bitsB.code (.cons (ofBits w) (ofBits acc)))).hd
      (Gives.cons (Gives.id _).hd
          (Gives.cons hd (Gives.cons (Gives.quote one _) (Gives.id _).tl.tl))) d1'
    have r0 := Does.run (Gives.id (θ := θ) (.cons bitsB.code (.cons (ofBits w) (ofBits acc)))).hd
      (Gives.cons (Gives.id _).hd
          (Gives.cons hd (Gives.cons (Gives.quote .nil _) (Gives.id _).tl.tl))) d0'
    refine ⟨Q1 ++ Q0, (Does.ite_true hnz e (Does.either r1 r0)).mono ?_, ?_, ?_⟩
    · have : max
        (2 + (2 + (1 + 3 + 1 + 20 * w.length + 2 + (1 + 3 + 1) + 1) + 1) + (n + 1) *
            (60 * w.length + 100) + 1)
          (2 + (2 + (1 + 3 + 1 + 20 * w.length + 2 + (1 + 3 + 1) + 1) + 1) + (n + 1) *
              (60 * w.length + 100) + 1) =
          2 + (2 + (1 + 3 + 1 + 20 * w.length + 2 + (1 + 3 + 1) + 1) + 1) + (n + 1) *
              (60 * w.length + 100) + 1 := max_self _
      have e2 : (n + 1 + 1) * (60 * w.length + 100) = (n + 1) * (60 * w.length + 100) +
          (60 * w.length + 100) := by ring
      omega
    · intro q hq
      rcases List.mem_append.1 hq with hq | hq
      · obtain ⟨u, hu, h⟩ := q1 q hq
        exact ⟨true :: u, List.mem_append_left _ (List.mem_map.2 ⟨u, hu, rfl⟩), by simp [h]⟩
      · obtain ⟨u, hu, h⟩ := q0 q hq
        exact ⟨false :: u, List.mem_append_right _ (List.mem_map.2 ⟨u, hu, rfl⟩), by simp [h]⟩
    · intro φ
      rw [wsum_append, v1, v0, allBits, List.map_append, List.sum_append, List.map_map,
          List.map_map]
      simp [Function.comp_def]

/-- Guess a bit list whose length is a fixed binary number. -/
@[expose] def bitsF (n : List Bool) : Fm :=
    app bitsB.code (.quote (.cons bitsB.code (.cons (ofBits n) .nil)))

theorem bitsF_does (n : List Bool) (x : Tree) : ∃ Q,
    Does θ (bitsF n) x Q ((KT.val n + 1) * (60 * n.length + 100) + 5) ∧
    (∀ q ∈ Q, ∃ u ∈ allBits (KT.val n), q.2 = ofBits u.reverse) ∧
    ∀ φ : Tree → A, wsum Q φ = ((allBits (KT.val n)).map fun u => φ (ofBits u.reverse)).sum := by
  obtain ⟨Q, d, h1, h2⟩ := bitsB_does (θ := θ) (KT.val n) n [] rfl
  have h := Does.app (p := bitsB.code) (R := fun _ => Q)
      (Gives.quote (θ := θ) (.cons bitsB.code (.cons (ofBits n) .nil)) x)
    (by
      intro q hq
      rw [List.mem_singleton] at hq
      subst hq
      rw [Fm.ofTree_code]
      exact d)
  refine ⟨Q, (h.congr ?_ fun φ => ?_).mono (by omega), ?_, ?_⟩
  · intro p hp
    obtain ⟨q, hq, r, hr, h3, h4⟩ := mem_bindW hp
    exact ⟨r, hr, h3.symm⟩
  · rw [wsum_bindW]
    simp
  · intro q hq
    obtain ⟨u, hu, h⟩ := h1 q hq
    exact ⟨u, hu, by simpa using h⟩
  · intro φ
    rw [h2]
    simp

end Bits

end Cslib.Circuits.Arithmetic.Separation.Interpreter
