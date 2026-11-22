/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.ProgPieces

/-!
# Closed programs

A program is closed in `n` variables if it refers only to the first `n` entries
of its environment (`Prog.closed n p = true`). Its meaning and its value bounds
are then unaffected by further entries (`eval_append`, `bounded_append`).

The explicit machine of a sum–product recursion is given by closed programs, and
`callT q args` runs such a program on argument terms inside a larger program.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.SumProduct

open NtimeDspace.ProgLang NtimeDspace.ProgTerm Term

namespace Prog'

/-- Whether a program refers only to its first `n` variables. -/
def closed : ℕ → Prog → Bool
  | _, .const _ => true
  | n, .var i => decide (i < n)
  | n, .add a b | n, .sub a b | n, .mul a b | n, .div a b | n, .mod a b | n, .bit a b
  | n, .lt a b => closed n a && closed n b
  | n, .input a => closed n a
  | n, .ite c t e => closed n c && closed n t && closed n e
  | n, .letIn a b => closed n a && closed (n + 1) b
  | n, .fold m i b => closed n m && closed n i && closed (n + 2) b

variable {w : List Bool}

theorem eval_append : ∀ (p : Prog) (env extra : List ℕ), closed env.length p = true →
    p.eval w (env ++ extra) = p.eval w env
  | .const _, _, _, _ => rfl
  | .var i, env, extra, h => by
    simp only [closed, decide_eq_true_eq] at h
    simp [Prog.eval, List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  | .add a b, env, extra, h | .sub a b, env, extra, h | .mul a b, env, extra, h
  | .div a b, env, extra, h | .mod a b, env, extra, h | .bit a b, env, extra, h
  | .lt a b, env, extra, h => by
    simp only [closed, Bool.and_eq_true] at h
    simp only [Prog.eval, eval_append a env extra h.1, eval_append b env extra h.2]
  | .input a, env, extra, h => by
    simp only [closed] at h
    simp only [Prog.eval, eval_append a env extra h]
  | .ite c t e, env, extra, h => by
    simp only [closed, Bool.and_eq_true] at h
    simp only [Prog.eval, eval_append c env extra h.1.1, eval_append t env extra h.1.2,
      eval_append e env extra h.2]
  | .letIn a b, env, extra, h => by
    simp only [closed, Bool.and_eq_true] at h
    simp only [Prog.eval, eval_append a env extra h.1]
    exact eval_append b (a.eval w env :: env) extra (by simpa using h.2)
  | .fold m i b, env, extra, h => by
    simp only [closed, Bool.and_eq_true] at h
    simp only [Prog.eval, eval_append m env extra h.1.1, eval_append i env extra h.1.2]
    congr 1
    funext acc k
    exact eval_append b (acc :: k :: env) extra (by simpa using h.2)

theorem foldAcc_append (b : Prog) (env extra : List ℕ) (h : closed (env.length + 2) b = true)
    (init k : ℕ) :
    Prog.foldAcc w b (env ++ extra) init k = Prog.foldAcc w b env init k := by
  unfold Prog.foldAcc
  congr 1
  funext acc i
  exact eval_append b (acc :: i :: env) extra (by simpa using h)

theorem bounded_append (B : ℕ) : ∀ (p : Prog) (env extra : List ℕ), closed env.length p = true →
    (p.Bounded w B (env ++ extra) ↔ p.Bounded w B env)
  | .const _, _, _, _ => Iff.rfl
  | .var _, _, _, _ => Iff.rfl
  | .add a b, env, extra, h | .mul a b, env, extra, h => by
    simp only [closed, Bool.and_eq_true] at h
    simp only [Prog.Bounded, bounded_append B a env extra h.1, bounded_append B b env extra h.2,
      Prog.eval, eval_append a env extra h.1, eval_append b env extra h.2]
  | .sub a b, env, extra, h | .div a b, env, extra, h | .mod a b, env, extra, h
  | .bit a b, env, extra, h | .lt a b, env, extra, h => by
    simp only [closed, Bool.and_eq_true] at h
    simp only [Prog.Bounded, bounded_append B a env extra h.1, bounded_append B b env extra h.2]
  | .input a, env, extra, h => by
    simp only [closed] at h
    simp only [Prog.Bounded, bounded_append B a env extra h]
  | .ite c t e, env, extra, h => by
    simp only [closed, Bool.and_eq_true] at h
    simp only [Prog.Bounded, bounded_append B c env extra h.1.1, bounded_append B t env extra h.1.2,
      bounded_append B e env extra h.2, eval_append c env extra h.1.1]
  | .letIn a b, env, extra, h => by
    simp only [closed, Bool.and_eq_true] at h
    simp only [Prog.Bounded, bounded_append B a env extra h.1, eval_append a env extra h.1]
    rw [show a.eval w env :: (env ++ extra) = (a.eval w env :: env) ++ extra from rfl,
      bounded_append B b (a.eval w env :: env) extra (by simpa using h.2)]
  | .fold m i b, env, extra, h => by
    simp only [closed, Bool.and_eq_true] at h
    simp only [Prog.Bounded, bounded_append B m env extra h.1.1, bounded_append B i env extra h.1.2,
      eval_append m env extra h.1.1, eval_append i env extra h.1.2,
      foldAcc_append b env extra h.2]
    refine and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ =>
      forall_congr' fun k => imp_congr_right fun _ => ?_
    exact bounded_append B b (_ :: k :: env) extra (by simpa using h.2)

end Prog'

/-! ### Running a closed program on arguments -/

/-- Run a program closed in two variables on two argument terms. -/
def callT2 (q : Prog) (a b : Term) : Term := fun d => .letIn (b d) (.letIn (a (d + 1)) q)

/-- Run a program closed in three variables on three argument terms. -/
def callT3 (q : Prog) (a b c : Term) : Term :=
  fun d => .letIn (c d) (.letIn (b (d + 1)) (.letIn (a (d + 2)) q))

variable {w : List Bool} {B : ℕ}

theorem lvl_denote_cons {a : ℕ} {env : List ℕ} (ha : a < env.length) (x : ℕ) :
    (lvl a).denote w (x :: env) = (lvl a).denote w env :=
  (ProgTerm.stableAt_lvl ha).cons x

theorem denote_callT2 {q : Prog} (hq : Prog'.closed 2 q = true) {a b : ℕ} {env : List ℕ}
    (ha : a < env.length) (hb : b < env.length) :
    (callT2 q (lvl a) (lvl b)).denote w env =
      q.eval w [(lvl a).denote w env, (lvl b).denote w env] := by
  show Prog.eval w (.letIn _ (.letIn _ q)) env = _
  simp only [Prog.eval]
  have e1 : (lvl a (env.length + 1)).eval w ((lvl b env.length).eval w env :: env) =
      (lvl a).denote w env := by
    rw [← lvl_denote_cons ha ((lvl b).denote w env)]; rfl
  rw [e1]
  exact Prog'.eval_append q [(lvl a).denote w env, (lvl b).denote w env] env hq

theorem bnd_callT2 {q : Prog} (hq : Prog'.closed 2 q = true) {a b : ℕ} {env : List ℕ}
    (ha : a < env.length) (hb : b < env.length)
    (h : q.Bounded w B [(lvl a).denote w env, (lvl b).denote w env]) :
    (callT2 q (lvl a) (lvl b)).Bnd w B env := by
  show Prog.Bounded w B (.letIn _ (.letIn _ q)) env
  simp only [Prog.Bounded]
  refine ⟨trivial, trivial, ?_⟩
  have e1 : (lvl a (env.length + 1)).eval w ((lvl b env.length).eval w env :: env) =
      (lvl a).denote w env := by
    rw [← lvl_denote_cons ha ((lvl b).denote w env)]; rfl
  rw [e1]
  exact (Prog'.bounded_append B q [(lvl a).denote w env, (lvl b).denote w env] env hq).mpr h

theorem denote_callT3 {q : Prog} (hq : Prog'.closed 3 q = true) {a b c : ℕ} {env : List ℕ}
    (ha : a < env.length) (hb : b < env.length) (hc : c < env.length) :
    (callT3 q (lvl a) (lvl b) (lvl c)).denote w env =
      q.eval w [(lvl a).denote w env, (lvl b).denote w env, (lvl c).denote w env] := by
  show Prog.eval w (.letIn _ (.letIn _ (.letIn _ q))) env = _
  simp only [Prog.eval]
  have e1 : (lvl b (env.length + 1)).eval w ((lvl c env.length).eval w env :: env) =
      (lvl b).denote w env := by
    rw [← lvl_denote_cons hb ((lvl c).denote w env)]; rfl
  have e2 : (lvl a (env.length + 2)).eval w ((lvl b).denote w env ::
      (lvl c env.length).eval w env :: env) = (lvl a).denote w env := by
    rw [← ProgTerm.StableAt.cons₂ (ProgTerm.stableAt_lvl ha) ((lvl b).denote w env)
      ((lvl c).denote w env)]; rfl
  rw [e1, e2]
  exact Prog'.eval_append q [(lvl a).denote w env, (lvl b).denote w env, (lvl c).denote w env]
    env hq

theorem bnd_callT3 {q : Prog} (hq : Prog'.closed 3 q = true) {a b c : ℕ} {env : List ℕ}
    (ha : a < env.length) (hb : b < env.length) (hc : c < env.length)
    (h : q.Bounded w B [(lvl a).denote w env, (lvl b).denote w env, (lvl c).denote w env]) :
    (callT3 q (lvl a) (lvl b) (lvl c)).Bnd w B env := by
  show Prog.Bounded w B (.letIn _ (.letIn _ (.letIn _ q))) env
  simp only [Prog.Bounded]
  refine ⟨trivial, trivial, trivial, ?_⟩
  have e1 : (lvl b (env.length + 1)).eval w ((lvl c env.length).eval w env :: env) =
      (lvl b).denote w env := by
    rw [← lvl_denote_cons hb ((lvl c).denote w env)]; rfl
  have e2 : (lvl a (env.length + 2)).eval w ((lvl b).denote w env ::
      (lvl c env.length).eval w env :: env) = (lvl a).denote w env := by
    rw [← ProgTerm.StableAt.cons₂ (ProgTerm.stableAt_lvl ha) ((lvl b).denote w env)
      ((lvl c).denote w env)]; rfl
  rw [e1, e2]
  exact (Prog'.bounded_append B q
    [(lvl a).denote w env, (lvl b).denote w env, (lvl c).denote w env] env hq).mpr h

end Cslib.Complexity.NtimeDspace.SumProduct
