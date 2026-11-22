/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.ProgLang

/-!
# Programs that know the input length

`Prog` has bounded folds only, so a term cannot find the length of its input.
`decidable_of_prog_len` runs a while loop that counts the input bits into
register `0` and then the compiled term with that register as its one
environment entry. So a term may use the input length as variable `0`.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.ProgLang

open _root_.Turing _root_.Turing.CounterProgram Structured Prog _root_.Turing.MultiTapeTM

/-- Count the input bits into register `0`, using register `1` as a flag. -/
def lengthStmt : Stmt :=
  .seq (.assign 1 (.const 1))
    (.loop (.const 0) (.reg 1)
      (.read (.reg 0) (.assign 0 (.add (.reg 0) (.const 1)))
        (.assign 0 (.add (.reg 0) (.const 1))) (.assign 1 (.const 0))))

theorem getD_set_ne' {l : List ℕ} {i j : ℕ} (v : ℕ) (h : j ≠ i) :
    (l.set i v).getD j 0 = l.getD j 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_set, Ne.symm h]

/-- The loop from position `i` with the flag set ends with register `0` at the length. -/
theorem lengthLoop_exec {w : List Bool} {B : ℕ} (hn : w.length ≤ B) (hB : 1 ≤ B) :
    ∀ d (r : List ℕ), w.length = r.getD 0 0 + d → r.getD 1 0 = 1 → 2 ≤ r.length → LeB B r →
      ∃ r', Exec w (LeB B) (.loop (.const 0) (.reg 1)
        (.read (.reg 0) (.assign 0 (.add (.reg 0) (.const 1)))
          (.assign 0 (.add (.reg 0) (.const 1))) (.assign 1 (.const 0)))) r r' ∧
        r'.length = r.length ∧ r'.getD 0 0 = w.length ∧
        (∀ j, 2 ≤ j → r'.getD j 0 = r.getD j 0) ∧ LeB B r' := by
  intro d
  induction d with
  | zero =>
    intro r hr hf hl hb
    have hend : w[(Expr.reg 0).eval r]? = none := by
      simp only [Expr.eval_reg]; exact List.getElem?_eq_none (by omega)
    set r1 := r.set 1 0
    have hb1 : LeB B r1 := by
      intro x hx
      rcases List.mem_or_eq_of_mem_set hx with hx | rfl
      · exact hb x hx
      · exact Nat.zero_le _
    refine ⟨r1, .loop_step hb (by simp only [Expr.eval_reg, Expr.eval_const]; omega)
        (.read_end hb hend (.assign hb)) hb1
      (.loop_done hb1 (by simp [r1, List.getD_eq_getElem?_getD, List.getElem?_set,
        show 1 < r.length by omega])), by simp [r1], ?_, ?_, hb1⟩
    · rw [show r1.getD 0 0 = r.getD 0 0 from getD_set_ne' _ (by omega)]; omega
    · intro j hj; exact getD_set_ne' _ (by omega)
  | succ d ih =>
    intro r hr hf hl hb
    have hlt : r.getD 0 0 < w.length := by omega
    set r1 := r.set 0 (r.getD 0 0 + 1)
    have hb1 : LeB B r1 := by
      intro x hx
      rcases List.mem_or_eq_of_mem_set hx with hx | rfl
      · exact hb x hx
      · omega
    have h0 : r1.getD 0 0 = r.getD 0 0 + 1 := by
      simp [r1, List.getD_eq_getElem?_getD, List.getElem?_set, show 0 < r.length by omega]
    have h1 : r1.getD 1 0 = 1 := by rw [getD_set_ne' _ (by omega)]; exact hf
    obtain ⟨r', e', l', v', fr', b'⟩ := ih r1 (by omega) h1 (by simp [r1]; omega) hb1
    have hev : (Expr.add (.reg 0) (.const 1)).eval r = r.getD 0 0 + 1 := by
      simp [Expr.eval, List.getD_eq_getElem?_getD]
    have hbody : Exec w (LeB B) (.read (.reg 0) (.assign 0 (.add (.reg 0) (.const 1)))
        (.assign 0 (.add (.reg 0) (.const 1))) (.assign 1 (.const 0))) r r1 := by
      have hr1 : r1 = r.set 0 ((Expr.add (.reg 0) (.const 1)).eval r) := by rw [hev]
      cases hw : w[r.getD 0 0]? with
      | none => exact absurd hw (by rw [List.getElem?_eq_getElem hlt]; simp)
      | some x =>
        cases x
        · exact hr1 ▸ .read_false hb (by simp only [Expr.eval_reg]; exact hw) (.assign hb)
            (hr1 ▸ hb1)
        · exact hr1 ▸ .read_true hb (by simp only [Expr.eval_reg]; exact hw) (.assign hb)
            (hr1 ▸ hb1)
    refine ⟨r', .loop_step hb (by simp only [Expr.eval_reg, Expr.eval_const]; omega) hbody hb1
        e', by simp [l', r1], v', ?_, b'⟩
    intro j hj
    rw [fr' j hj]; exact getD_set_ne' _ (by omega)

/-- **A term that may read the input length** (as variable `0`) and decides `L`
with values below `2^K` gives a decider in simultaneous time `2^(C*budget)` and
space `C*budget`. -/
theorem decidable_of_prog_len {α : Type} {enc : α ↪ List Bool} (L : Set α) (P : Prog)
    (budget K : α → ℕ) (c : ℕ)
    (logarithmic : ∀ a, (enc a).length.log2 + 1 ≤ budget a)
    (K_pos : ∀ a, 1 ≤ K a) (K_le : ∀ a, K a ≤ c * budget a)
    (len_le : ∀ a, (enc a).length ≤ 2 ^ K a)
    (bounded : ∀ a, P.Bounded (enc a) (2 ^ K a) [(enc a).length])
    (decides : ∀ a, (1 ≤ P.eval (enc a) [(enc a).length] ↔ a ∈ L)) :
    ∃ C, DecidableInTimeAndSpace L enc (fun a => 2 ^ (C * budget a)) (fun a => C * budget a) := by
  set R := P.span + 4
  have hbudget (a : α) : 1 ≤ budget a := (Nat.le_add_left _ _).trans (logarithmic a)
  have hreg (a : α) {x : List ℕ} (hx : LeB (2 ^ K a) x) (hl : x.length = R) :
      (encList encNat x).length ≤ (R * (2 * c + 3)) * budget a := by
    refine (encList_le_of_LeB hx).trans ?_
    rw [hl, Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ (by nlinarith [K_le a, hbudget a])
  have hB (a : α) : 2 ≤ 2 ^ K a := by
    have := Nat.pow_le_pow_right (by norm_num : 0 < 2) (K_pos a); simpa using this
  have run (a : α) : ∃ final, Exec (enc a) (LeB (2 ^ K a))
      (.seq lengthStmt (P.compile [0] 2 3)) (List.replicate R 0) final ∧
      final.length = R ∧ final.getD 2 0 = P.eval (enc a) [(enc a).length] ∧
      LeB (2 ^ K a) final := by
    set r0 : List ℕ := List.replicate R 0
    have hz : LeB (2 ^ K a) r0 := fun x hx => by
      rw [List.eq_of_mem_replicate hx]; exact Nat.zero_le _
    set r1 := r0.set 1 1
    have hb1 : LeB (2 ^ K a) r1 := by
      intro x hx
      rcases List.mem_or_eq_of_mem_set hx with hx | rfl
      · exact hz x hx
      · exact (hB a).trans' (by norm_num)
    have hlen1 : r1.length = R := by simp [r1, r0]
    obtain ⟨r2, e2, l2, v2, -, b2⟩ := lengthLoop_exec (w := enc a) (len_le a)
        ((hB a).trans' (by norm_num))
      (enc a).length r1
      (by simp [r1, r0, List.getD_eq_getElem?_getD, List.getElem?_set, List.getElem?_replicate, R])
      (by simp [r1, r0, List.getD_eq_getElem?_getD, List.getElem?_set, R])
      (by rw [hlen1]; omega) hb1
    obtain ⟨r3, e3, l3, v3, -, b3⟩ := compile_correct (w := enc a) (B := 2 ^ K a) (hB a)
      P [(enc a).length] [0] 2 3 r2
      ⟨rfl, fun i hi => by
        simp only [List.length_singleton, Nat.lt_one_iff] at hi
        subst hi; simpa using v2⟩
      (by omega) (by rw [l2, hlen1]; omega) b2 (bounded a)
    exact ⟨r3, .seq (.seq (.assign hz) e2) e3, by rw [l3, l2, hlen1], v3, b3⟩
  choose final hfinal using run
  refine Structured.decidable_of_exec L (.seq lengthStmt (P.compile [0] 2 3)) 2 R budget
    (R * (2 * c + 3)) logarithmic final (fun a => ?_) (fun a => ?_) (fun a => ?_)
  · obtain ⟨e, -⟩ := hfinal a
    exact (exec_weaken e fun x hx hl => hreg a hx (by simpa using hl)).1
  · obtain ⟨_, l, _, b⟩ := hfinal a
    exact hreg a b l
  · obtain ⟨_, _, v, _⟩ := hfinal a
    rw [v]; exact decides a

end Cslib.Complexity.NtimeDspace.ProgLang
