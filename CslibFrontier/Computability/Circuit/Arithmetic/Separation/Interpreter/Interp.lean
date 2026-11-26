/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Interpreter.Budget

/-!
# Formulas for counting the names of constants

Building blocks of the interpreter `Interpreter.IF`: formulas that walk a budget along a word
(`Interpreter.DW`), compare (`Interpreter.DC`), and check that budgets are used up
(`Interpreter.AW`, `Interpreter.AZ`), with their evaluation lemmas. These formulas are plain:
they use no named constants.

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], module `NS1.Interp`.

## Main results

* `Interpreter.DW_some`, `Interpreter.DW_none`, `Interpreter.AW_ev`, `Interpreter.AZ_ev`.
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Interpreter

open Cslib.Circuits.Arithmetic.Separation.Interpreter.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A}

theorem Dt.ite_true {a b c : Fm} {x o p : Tree} {k j : ℕ} (ha : Dt θ a x o k) (ho : o ≠ .nil)
    (hb : Dt θ b x p j) :
    Dt θ (.ite a b c) x p (k + 1 + j) := Ev.ite_true (c := c) ha ho hb

theorem Dt.ite_false {a b c : Fm} {x p : Tree} {k j : ℕ} (ha : Dt θ a x .nil k)
    (hc : Dt θ c x p j) :
    Dt θ (.ite a b c) x p (k + 1 + j) := Ev.ite_false (b := b) ha hc

theorem Dt.run {a b : Fm} {x p d o : Tree} {k j i : ℕ} (ha : Dt θ a x p k) (hb : Dt θ b x d j)
    (h : Dt θ (Fm.ofTree p) d o i) : Dt θ (.run a b) x o (k + j + 1 + i) := Ev.run_det ha hb h

theorem Ev.ite_true_nil {a b c : Fm} {x o : Tree} {k : ℕ} (ha : Dt θ a x o k) (ho : o ≠ .nil)
    (hb : Ev θ b x []) : Ev θ (.ite a b c) x [] := Ev.ite_true (c := c) ha ho hb

theorem Ev.ite_false_nil {a b c : Fm} {x : Tree} {k : ℕ} (ha : Dt θ a x .nil k)
    (hc : Ev θ c x []) : Ev θ (.ite a b c) x [] := Ev.ite_false (b := b) ha hc

theorem Ev.run_nil {a b : Fm} {x p d : Tree} {k j : ℕ} (ha : Dt θ a x p k) (hb : Dt θ b x d j)
    (h : Ev θ (Fm.ofTree p) d []) : Ev θ (.run a b) x [] := Ev.run_det ha hb h

theorem Ev.cons_nil_left {a b : Fm} {x : Tree} {l : List (Run A)} (ha : Ev θ a x [])
    (hb : Ev θ b x l) :
    Ev θ (.cons a b) x [] := Ev.cons ha hb

theorem Ev.cons_nil_right {a b : Fm} {x : Tree} {l : List (Run A)} (ha : Ev θ a x l)
    (hb : Ev θ b x []) :
    Ev θ (.cons a b) x [] :=
  (List.flatMap_eq_nil_iff.2 fun _ _ => rfl) ▸ Ev.cons ha hb

private theorem dt_ofTree_code {a : Fm} {x o : Tree} {k : ℕ} (h : Dt θ a x o k) :
    Dt θ (Fm.ofTree a.code) x o k := by
  rwa [Fm.ofTree_code]

private theorem ev_hd_cons_ofTree_code {a : Fm} {y x : Tree} {l : List (Run A)} (h : Ev θ a x l) :
    Ev θ (Fm.ofTree (Tree.cons a.code y).hd) x l := by
  simpa only [hd_cons, Fm.ofTree_code] using h

section Programs

/-- Subtract 1 from a number; the argument is (this program, the number). -/
@[expose] def DW : Fm := .ite (.tl .id)
  (.ite (.hd (.tl .id)) (.cons (.quote .nil) (.tl (.tl .id)))
    (.cons (.quote one) (.run (.hd .id) (.cons (.hd .id) (.tl (.tl .id)))))) .fail

theorem DW_some {w w' : List Bool} (h : decw w = some w') :
    ∃ k ≤ 20 * w.length, Dt θ DW (.cons DW.code (ofBits w)) (ofBits w') k := by
  induction w generalizing w' with
  | nil => simp [decw] at h
  | cons b w ih =>
    cases b with
    | true =>
      simp only [decw, Option.some.injEq] at h
      subst h
      exact ⟨_, by simp only [List.length_cons]; omega,
          Dt.ite_true (.tl (.id _)) (by simp [ofBits]) (Dt.ite_true (.hd (.tl (.id _)))
        (by simp [ofBits, bit, one]) (.cons (.quote _ _) (.tl (.tl (.id _)))))⟩
    | false =>
      simp only [decw, Option.map_eq_some_iff] at h
      obtain ⟨v, hv, rfl⟩ := h
      obtain ⟨k, hk, hd⟩ := ih hv
      exact ⟨_, by simp only [List.length_cons]; omega,
          Dt.ite_true (.tl (.id _)) (by simp [ofBits]) (Dt.ite_false (.hd (.tl (.id _)))
        (.cons (.quote _ _) (.run (.hd (.id _)) (.cons (.hd (.id _)) (.tl (.tl (.id _))))
          (dt_ofTree_code hd))))⟩

theorem DW_none {w : List Bool} (h : decw w = none) : Ev θ DW (.cons DW.code (ofBits w)) [] := by
  induction w with
  | nil => exact Ev.ite_false_nil (.tl (.id _)) (.fail _)
  | cons b w ih =>
    cases b with
    | true => simp [decw] at h
    | false =>
      simp only [decw, Option.map_eq_none_iff] at h
      exact Ev.ite_true_nil (.tl (.id _)) (by simp [ofBits]) (Ev.ite_false_nil (.hd (.tl (.id _)))
        (Ev.cons_nil_right (.quote _ _)
          (Ev.run_nil (.hd (.id _)) (.cons (.hd (.id _)) (.tl (.tl (.id _))))
            (ev_hd_cons_ofTree_code (ih h)))))

/-- Subtract 1 in a budget; the argument is (this program, (the name, the budget)). -/
@[expose] def DC : Fm :=
  .ite (.tl (.tl .id))
    (.ite (.hd (.tl (.tl .id)))
      (.ite (.hd (.tl .id))
        (.ite (.hd (.hd (.tl .id)))
          (.cons (.cons (.hd (.hd (.tl (.tl .id)))) (.run (.hd .id) (.cons (.hd .id)
            (.cons (.tl (.hd (.tl .id))) (.tl (.hd (.tl (.tl .id)))))))) (.quote .nil))
          (.cons (.cons (.run (.hd .id) (.cons (.hd .id)
            (.cons (.tl (.hd (.tl .id))) (.hd (.hd (.tl (.tl .id)))))))
                (.tl (.hd (.tl (.tl .id))))) (.quote .nil)))
        .fail)
      (.ite (.hd (.tl .id)) .fail
        (.cons (.quote .nil)
            (.run (.quote DW.code) (.cons (.quote DW.code) (.tl (.tl (.tl .id))))))))
    .fail

theorem DC_some {t t' : Bt} {x : Tree} (h : Bt.dec x.path t = some t') :
    ∃ k ≤ 60 * t.ht, Dt θ DC (.cons DC.code (.cons x t.enc)) t'.enc k := by
  induction t generalizing x t' with
  | none => simp [Bt.dec] at h
  | leaf w =>
    cases x with
    | cons a b => simp [path, Bt.dec] at h
    | nil =>
      simp only [path, Bt.dec, Option.map_eq_some_iff] at h
      obtain ⟨v, hv, rfl⟩ := h
      obtain ⟨k, hk, hd⟩ := DW_some (θ := θ) hv
      exact ⟨_, by simp only [Bt.ht]; omega,
          Dt.ite_true (.tl (.tl (.id _))) (by simp [Bt.enc]) (Dt.ite_false (.hd (.tl (.tl (.id _))))
        (Dt.ite_false (.hd (.tl (.id _))) (.cons (.quote _ _) (.run (.quote _ _) (.cons (.quote _ _)
          (.tl (.tl (.tl (.id _))))) (dt_ofTree_code hd)))))⟩
  | node l r ihl ihr =>
    cases x with
    | nil => simp [path, Bt.dec] at h
    | cons a b =>
      by_cases ha : a = .nil
      · subst ha
        simp only [path, ne_eq, not_true_eq_false, decide_false, Bt.dec, Option.map_eq_some_iff]
            at h
        obtain ⟨v, hv, rfl⟩ := h
        obtain ⟨k, hk, hd⟩ := ihl hv
        exact ⟨_, by simp only [Bt.ht]; omega,
            Dt.ite_true (.tl (.tl (.id _))) (by simp [Bt.enc])
                (Dt.ite_true (.hd (.tl (.tl (.id _))))
          (by simp [Bt.enc])
              (Dt.ite_true (.hd (.tl (.id _))) (by simp) (Dt.ite_false (.hd (.hd (.tl (.id _))))
            (.cons (.cons (.run (.hd (.id _)) (.cons (.hd (.id _)) (.cons (.tl (.hd (.tl (.id _))))
              (.hd (.hd (.tl (.tl (.id _))))))) (dt_ofTree_code hd))
                (.tl (.hd (.tl (.tl (.id _))))))
                  (.quote _ _)))))⟩
      · simp only [path, ne_eq, ha, not_false_eq_true, decide_true, Bt.dec, Option.map_eq_some_iff]
          at h
        obtain ⟨v, hv, rfl⟩ := h
        obtain ⟨k, hk, hd⟩ := ihr hv
        exact ⟨_, by simp only [Bt.ht]; omega,
            Dt.ite_true (.tl (.tl (.id _))) (by simp [Bt.enc])
                (Dt.ite_true (.hd (.tl (.tl (.id _))))
          (by simp [Bt.enc])
              (Dt.ite_true (.hd (.tl (.id _))) (by simp) (Dt.ite_true (.hd (.hd (.tl (.id _))))
            (by simpa using ha)
                (.cons (.cons (.hd (.hd (.tl (.tl (.id _)))))
                    (.run (.hd (.id _)) (.cons (.hd (.id _))
              (.cons (.tl (.hd (.tl (.id _)))) (.tl (.hd (.tl (.tl (.id _)))))))
                (dt_ofTree_code hd))) (.quote _ _)))))⟩

theorem DC_none {t : Bt} {x : Tree} (h : Bt.dec x.path t = none) : Ev θ DC
    (.cons DC.code (.cons x t.enc)) [] := by
  induction t generalizing x with
  | none => exact Ev.ite_false_nil (.tl (.tl (.id _))) (.fail _)
  | leaf w =>
    refine Ev.ite_true_nil (.tl (.tl (.id _))) (by simp [Bt.enc])
        (Ev.ite_false_nil (.hd (.tl (.tl (.id _)))) ?_)
    cases x with
    | cons a b => exact Ev.ite_true_nil (.hd (.tl (.id _))) (by simp) (.fail _)
    | nil =>
      simp only [path, Bt.dec, Option.map_eq_none_iff] at h
      refine Ev.ite_false_nil (.hd (.tl (.id _)))
          (Ev.cons_nil_right (.quote _ _) (Ev.run_nil (.quote _ _)
        (.cons (.quote _ _) (.tl (.tl (.tl (.id _))))) ?_))
      simp only [Fm.ofTree_code]
      exact DW_none h
  | node l r ihl ihr =>
    refine Ev.ite_true_nil (.tl (.tl (.id _))) (by simp [Bt.enc])
        (Ev.ite_true_nil (.hd (.tl (.tl (.id _))))
      (by simp [Bt.enc]) ?_)
    cases x with
    | nil => exact Ev.ite_false_nil (.hd (.tl (.id _))) (.fail _)
    | cons a b =>
      refine Ev.ite_true_nil (.hd (.tl (.id _))) (by simp) ?_
      by_cases ha : a = .nil
      · subst ha
        simp only [path, ne_eq, not_true_eq_false, decide_false, Bt.dec, Option.map_eq_none_iff]
            at h
        exact Ev.ite_false_nil (.hd (.hd (.tl (.id _))))
            (Ev.cons_nil_left (Ev.cons_nil_left (Ev.run_nil (.hd (.id _))
          (.cons (.hd (.id _)) (.cons (.tl (.hd (.tl (.id _)))) (.hd (.hd (.tl (.tl (.id _)))))))
              (ev_hd_cons_ofTree_code (ihl h)))
          (Dt.tl (.hd (.tl (.tl (.id _)))))) (Dt.quote _ _))
      · simp only [path, ne_eq, ha, not_false_eq_true, decide_true, Bt.dec, Option.map_eq_none_iff]
          at h
        exact Ev.ite_true_nil (.hd (.hd (.tl (.id _)))) (by simpa using ha)
            (Ev.cons_nil_left (Ev.cons_nil_right
          (Dt.hd (.hd (.tl (.tl (.id _))))) (Ev.run_nil (.hd (.id _)) (.cons (.hd (.id _))
          (.cons (.tl (.hd (.tl (.id _)))) (.tl (.hd (.tl (.tl (.id _)))))))
            (ev_hd_cons_ofTree_code (ihr h)))) (Dt.quote _ _))

/-- Check that a number is 0. -/
@[expose] def AW : Fm := .ite (.tl .id)
  (.ite (.hd (.tl .id)) .fail (.run (.hd .id) (.cons (.hd .id) (.tl (.tl .id))))) (.quote .nil)

theorem AW_ev (w : List Bool) : ∃ k ≤ 20 * w.length + 5, ∃ o, Ev θ AW (.cons AW.code (ofBits w))
    (if w.all (! ·) then [.det k o] else []) := by
  induction w with
  | nil => exact ⟨_, by omega, _, Dt.ite_false (.tl (.id _)) (.quote _ _)⟩
  | cons b w ih =>
    obtain ⟨k, hk, o, ih⟩ := ih
    cases b with
    | true =>
      refine ⟨0, Nat.zero_le _, .nil, ?_⟩
      simp only [List.all_cons, Bool.not_true, Bool.false_and, Bool.false_eq_true, ite_false]
      exact Ev.ite_true_nil (.tl (.id _)) (by simp [ofBits]) (Ev.ite_true_nil (.hd (.tl (.id _)))
        (by simp [ofBits, bit, one]) (.fail _))
    | false =>
      simp only [List.all_cons, Bool.not_false, Bool.true_and]
      by_cases h : w.all (! ·)
      · simp only [h, ite_true] at ih ⊢
        exact ⟨_, by simp only [List.length_cons]; omega, o,
            Dt.ite_true (.tl (.id _)) (by simp [ofBits]) (Dt.ite_false (.hd (.tl (.id _)))
          (.run (.hd (.id _)) (.cons (.hd (.id _)) (.tl (.tl (.id _)))) (dt_ofTree_code ih)))⟩
      · simp only [h] at ih ⊢
        exact ⟨0, Nat.zero_le _, .nil, Ev.ite_true_nil (.tl (.id _)) (by simp [ofBits])
            (Ev.ite_false_nil (.hd (.tl (.id _)))
          (Ev.run_nil (.hd (.id _)) (.cons (.hd (.id _)) (.tl (.tl (.id _))))
            (ev_hd_cons_ofTree_code ih)))⟩

/-- Check that all numbers of a budget are 0. -/
@[expose] def AZ : Fm := .ite (.tl .id)
  (.ite (.hd (.tl .id))
    (.cons (.run (.hd .id) (.cons (.hd .id) (.hd (.hd (.tl .id)))))
      (.run (.hd .id) (.cons (.hd .id) (.tl (.hd (.tl .id))))))
    (.run (.quote AW.code) (.cons (.quote AW.code) (.tl (.tl .id)))))
  (.quote .nil)

theorem AZ_ev (t : Bt) : ∃ k ≤ 40 * t.nds, ∃ o,
    Ev θ AZ (.cons AZ.code t.enc) (if t.zero then [.det k o] else []) := by
  induction t with
  | none => exact ⟨_, by simp [Bt.nds], _, Dt.ite_false (.tl (.id _)) (.quote _ _)⟩
  | leaf w =>
    obtain ⟨k, hk, o, h⟩ := AW_ev (θ := θ) w
    simp only [Bt.zero]
    by_cases hz : w.all (! ·)
    · simp only [hz, ite_true] at h ⊢
      exact ⟨_, by simp only [Bt.nds]; omega, o,
          Dt.ite_true (.tl (.id _)) (by simp [Bt.enc]) (Dt.ite_false (.hd (.tl (.id _)))
        (.run (.quote _ _) (.cons (.quote _ _) (.tl (.tl (.id _)))) (dt_ofTree_code h)))⟩
    · simp only [hz] at h ⊢
      exact ⟨0, Nat.zero_le _, .nil, Ev.ite_true_nil (.tl (.id _)) (by simp [Bt.enc])
        (Ev.ite_false_nil (.hd (.tl (.id _)))
          (Ev.run_nil (.quote _ _) (.cons (.quote _ _) (.tl (.tl (.id _))))
            ((Fm.ofTree_code AW).symm ▸ h)))⟩
  | node l r ihl ihr =>
    obtain ⟨kl, hkl, ol, hl⟩ := ihl
    obtain ⟨kr, hkr, or, hr⟩ := ihr
    have erun (arg : Fm) {t : Bt} {kt : ℕ} {ot : Tree}
        (hs : Dt θ (.cons (.hd .id) arg) (.cons AZ.code (Bt.node l r).enc)
          (.cons AZ.code t.enc) 7)
        (ht : Ev θ AZ (.cons AZ.code t.enc) (if t.zero then [.det kt ot] else [])) :
        Ev θ (.run (.hd .id) (.cons (.hd .id) arg)) (.cons AZ.code (Bt.node l r).enc)
          ((if t.zero then [.det kt ot] else []).map (Run.delay 10)) :=
      Ev.run_det (k := 2) (j := 7) (.hd (.id _)) hs (ev_hd_cons_ofTree_code ht)
    have el := erun (.hd (.hd (.tl .id))) (.cons (.hd (.id _)) (.hd (.hd (.tl (.id _))))) hl
    have er := erun (.tl (.hd (.tl .id))) (.cons (.hd (.id _)) (.tl (.hd (.tl (.id _))))) hr
    simp only [Bt.zero]
    by_cases hzl : l.zero
    · by_cases hzr : r.zero
      · simp only [hzl, hzr, ite_true, Bool.and_self] at el er ⊢
        exact ⟨_, by simp only [Bt.nds]; omega, _,
            Dt.ite_true (.tl (.id _)) (by simp [Bt.enc]) (Dt.ite_true (.hd (.tl (.id _)))
          (by simp [Bt.enc]) (Dt.cons (k := 10 + kl) (j := 10 + kr) el er))⟩
      · simp only [hzl, hzr, ite_true, ite_false, Bool.and_false, Bool.false_eq_true, List.map_nil]
          at el er ⊢
        exact ⟨0, Nat.zero_le _, .nil, Ev.ite_true_nil (.tl (.id _)) (by simp [Bt.enc])
          (Ev.ite_true_nil (.hd (.tl (.id _))) (by simp [Bt.enc]) (Ev.cons_nil_right el er))⟩
    · simp only [hzl, ite_false, Bool.false_and, Bool.false_eq_true, List.map_nil] at el er ⊢
      exact ⟨0, Nat.zero_le _, .nil, Ev.ite_true_nil (.tl (.id _)) (by simp [Bt.enc])
        (Ev.ite_true_nil (.hd (.tl (.id _))) (by simp [Bt.enc]) (Ev.cons_nil_left el er))⟩

end Programs

end Cslib.Circuits.Arithmetic.Separation.Interpreter
