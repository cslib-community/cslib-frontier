/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.ProgLang

/-!
# Terms with named binders

`Term` builds `Prog` terms whose variables are de Bruijn *levels*: a binder
created at environment depth `d` is the term `lvl d`, which becomes the
index `depth - d - 1` wherever it is used. Bodies of `letT` and `foldT` are
Lean functions of their bound variables, so sub-terms may refer to outer
variables without manual index shifting.

`denote` is the meaning of a term in an environment, and `Bnd` says that every
value arising in its evaluation is at most `B`. Both have one lemma per
combinator, so the meaning of a program is computed by `simp`.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.ProgTerm

open ProgLang

/-- A term, built at a given environment depth. -/
def Term : Type := ℕ → ProgLang.Prog

namespace Term

/-- The meaning of a term. -/
def denote (w : List Bool) (t : Term) (env : List ℕ) : ℕ := (t env.length).eval w env

/-- Every value arising in the evaluation is at most `B`. -/
def Bnd (w : List Bool) (B : ℕ) (t : Term) (env : List ℕ) : Prop :=
  (t env.length).Bounded w B env

/-- The variable bound at level `l`. -/
def lvl (l : ℕ) : Term := fun d => .var (d - l - 1)
/-- The constant `k`. -/
def const (k : ℕ) : Term := fun _ => .const k
/-- The sum `a + b`. -/
def add (a b : Term) : Term := fun d => .add (a d) (b d)
/-- The truncated difference `a - b`. -/
def sub (a b : Term) : Term := fun d => .sub (a d) (b d)
/-- The product `a * b`. -/
def mul (a b : Term) : Term := fun d => .mul (a d) (b d)
/-- The floor quotient `a / b` (`0` when `b = 0`). -/
def div (a b : Term) : Term := fun d => .div (a d) (b d)
/-- The remainder `a % b` (`a` when `b = 0`). -/
def mod (a b : Term) : Term := fun d => .mod (a d) (b d)
/-- Bit `i` of `a`, as `0` or `1`. -/
def bit (a i : Term) : Term := fun d => .bit (a d) (i d)
/-- The comparison `a < b`, as `1` if true and `0` otherwise. -/
def lt (a b : Term) : Term := fun d => .lt (a d) (b d)
/-- The input bit at position `a`: `1`, `0`, or `2` past the end of the input. -/
def input (a : Term) : Term := fun d => .input (a d)
/-- The conditional: `t` if `c` is positive, and `e` otherwise. -/
def ite (c t e : Term) : Term := fun d => .ite (c d) (t d) (e d)
/-- `letT a f` binds the value of `a` to a new variable and evaluates `f` at it. -/
def letT (a : Term) (f : Term → Term) : Term := fun d => .letIn (a d) (f (lvl d) (d + 1))
/-- `foldT n init f` iterates `acc ← f acc i` for `i < n`. -/
def foldT (n init : Term) (f : Term → Term → Term) : Term :=
  fun d => .fold (n d) (init d) (f (lvl (d + 1)) (lvl d) (d + 2))

variable (w : List Bool) (B : ℕ)

theorem denote_lvl (l : ℕ) (env : List ℕ) :
    (lvl l).denote w env = env.getD (env.length - l - 1) 0 := rfl

theorem le_length_cons {l x : ℕ} {env : List ℕ} (h : l ≤ env.length) :
    l ≤ (x :: env).length := by simp; omega

/-- Variables are resolved one binder at a time. -/
theorem denote_lvl_cons (l x : ℕ) (env : List ℕ) (h : l ≤ env.length) :
    (lvl l).denote w (x :: env) = if l = env.length then x else (lvl l).denote w env := by
  simp only [denote_lvl, List.length_cons]
  split_ifs with hl
  · subst hl; simp
  · rw [show env.length + 1 - l - 1 = (env.length - l - 1) + 1 by omega, List.getD_cons_succ]
@[simp] theorem denote_const (k : ℕ) (env : List ℕ) : (const k).denote w env = k := rfl
@[simp] theorem denote_add (a b : Term) (env : List ℕ) :
    (add a b).denote w env = a.denote w env + b.denote w env := rfl
@[simp] theorem denote_sub (a b : Term) (env : List ℕ) :
    (sub a b).denote w env = a.denote w env - b.denote w env := rfl
@[simp] theorem denote_mul (a b : Term) (env : List ℕ) :
    (mul a b).denote w env = a.denote w env * b.denote w env := rfl
@[simp] theorem denote_div (a b : Term) (env : List ℕ) :
    (div a b).denote w env = a.denote w env / b.denote w env := rfl
@[simp] theorem denote_mod (a b : Term) (env : List ℕ) :
    (mod a b).denote w env = a.denote w env % b.denote w env := rfl
@[simp] theorem denote_bit (a i : Term) (env : List ℕ) :
    (bit a i).denote w env = ((a.denote w env).testBit (i.denote w env)).toNat := rfl
@[simp] theorem denote_lt (a b : Term) (env : List ℕ) :
    (lt a b).denote w env = if a.denote w env < b.denote w env then 1 else 0 := rfl
@[simp] theorem denote_input (a : Term) (env : List ℕ) :
    (input a).denote w env = Prog.inputValue w (a.denote w env) := rfl
@[simp] theorem denote_ite (c t e : Term) (env : List ℕ) :
    (ite c t e).denote w env =
      if 0 < c.denote w env then t.denote w env else e.denote w env := rfl
@[simp] theorem denote_letT (a : Term) (f : Term → Term) (env : List ℕ) :
    (letT a f).denote w env = (f (lvl env.length)).denote w (a.denote w env :: env) := rfl

/-- The accumulator of a fold after `k` steps. -/
def foldAcc (f : Term → Term → Term) (env : List ℕ) (init : ℕ) (k : ℕ) : ℕ :=
  (List.range k).foldl
    (fun acc i => (f (lvl (env.length + 1)) (lvl env.length)).denote w (acc :: i :: env)) init

@[simp] theorem foldAcc_zero (f : Term → Term → Term) (env : List ℕ) (init : ℕ) :
    foldAcc w f env init 0 = init := rfl

theorem foldAcc_succ (f : Term → Term → Term) (env : List ℕ) (init k : ℕ) :
    foldAcc w f env init (k + 1) =
      (f (lvl (env.length + 1)) (lvl env.length)).denote w
          (foldAcc w f env init k :: k :: env) := by
  simp [foldAcc, List.range_succ, List.foldl_append]

@[simp] theorem denote_foldT (n init : Term) (f : Term → Term → Term) (env : List ℕ) :
    (foldT n init f).denote w env = foldAcc w f env (init.denote w env) (n.denote w env) := rfl

@[simp] theorem bnd_lvl (l : ℕ) (env : List ℕ) : (lvl l).Bnd w B env := trivial
@[simp] theorem bnd_const (k : ℕ) (env : List ℕ) : (const k).Bnd w B env ↔ k ≤ B := Iff.rfl
@[simp] theorem bnd_add (a b : Term) (env : List ℕ) :
    (add a b).Bnd w B env ↔
      a.Bnd w B env ∧ b.Bnd w B env ∧ a.denote w env + b.denote w env ≤ B := Iff.rfl
@[simp] theorem bnd_sub (a b : Term) (env : List ℕ) :
    (sub a b).Bnd w B env ↔ a.Bnd w B env ∧ b.Bnd w B env := Iff.rfl
@[simp] theorem bnd_mul (a b : Term) (env : List ℕ) :
    (mul a b).Bnd w B env ↔
      a.Bnd w B env ∧ b.Bnd w B env ∧ a.denote w env * b.denote w env ≤ B := Iff.rfl
@[simp] theorem bnd_div (a b : Term) (env : List ℕ) :
    (div a b).Bnd w B env ↔ a.Bnd w B env ∧ b.Bnd w B env := Iff.rfl
@[simp] theorem bnd_mod (a b : Term) (env : List ℕ) :
    (mod a b).Bnd w B env ↔ a.Bnd w B env ∧ b.Bnd w B env := Iff.rfl
@[simp] theorem bnd_bit (a i : Term) (env : List ℕ) :
    (bit a i).Bnd w B env ↔ a.Bnd w B env ∧ i.Bnd w B env := Iff.rfl
@[simp] theorem bnd_lt (a b : Term) (env : List ℕ) :
    (lt a b).Bnd w B env ↔ a.Bnd w B env ∧ b.Bnd w B env := Iff.rfl
@[simp] theorem bnd_input (a : Term) (env : List ℕ) :
    (input a).Bnd w B env ↔ a.Bnd w B env := Iff.rfl
@[simp] theorem bnd_ite (c t e : Term) (env : List ℕ) :
    (ite c t e).Bnd w B env ↔ c.Bnd w B env ∧
      (if 0 < c.denote w env then t.Bnd w B env else e.Bnd w B env) := Iff.rfl
@[simp] theorem bnd_letT (a : Term) (f : Term → Term) (env : List ℕ) :
    (letT a f).Bnd w B env ↔
      a.Bnd w B env ∧ (f (lvl env.length)).Bnd w B (a.denote w env :: env) := Iff.rfl
@[simp] theorem bnd_foldT (n init : Term) (f : Term → Term → Term) (env : List ℕ) :
    (foldT n init f).Bnd w B env ↔ n.Bnd w B env ∧ init.Bnd w B env ∧ n.denote w env ≤ B ∧
      ∀ k < n.denote w env, (f (lvl (env.length + 1)) (lvl env.length)).Bnd w B
        (foldAcc w f env (init.denote w env) k :: k :: env) := Iff.rfl

/-! ### Derived combinators -/

/-- `2 ^ e`. -/
def pow2 (e : Term) : Term := foldT e (const 1) fun acc _ => mul acc (const 2)

theorem foldAcc_pow2 (env : List ℕ) (k : ℕ) :
    foldAcc w (fun acc _ => mul acc (const 2)) env 1 k = 2 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [foldAcc_succ]
    simp [denote_lvl, Nat.add_assoc, Nat.add_sub_add_left, ih, pow_succ]

@[simp] theorem denote_pow2 (e : Term) (env : List ℕ) :
    (pow2 e).denote w env = 2 ^ e.denote w env := by
  simp [pow2, foldAcc_pow2]

theorem bnd_pow2 (e : Term) (env : List ℕ) (he : e.Bnd w B env)
    (hb : 2 ^ e.denote w env ≤ B) : (pow2 e).Bnd w B env := by
  have hle : e.denote w env ≤ B :=
    (Nat.lt_two_pow_self).le.trans hb
  simp only [pow2, bnd_foldT, bnd_const, bnd_mul, bnd_lvl, true_and]
  refine ⟨he, (Nat.one_le_two_pow).trans hb, hle, fun k hk => ?_⟩
  simp only [denote_lvl_cons, List.length_cons, le_refl, ite_true, denote_const,
    foldAcc_pow2]
  rw [← pow_succ]
  have hk' : 2 ^ (k + 1) ≤ B := (Nat.pow_le_pow_right (by norm_num) hk).trans hb
  exact ⟨(Nat.le_self_pow (by omega) 2).trans hk', hk'⟩

/-- `(∑_{i<n} body i) mod p`, reducing after every step. -/
def sumMod (p n : Term) (body : Term → Term) : Term :=
  foldT n (const 0) fun acc i => mod (add acc (body i)) p

/-- `(∏_{i<n} body i) mod p`, reducing after every step. -/
def prodMod (p n : Term) (body : Term → Term) : Term :=
  foldT n (const 1) fun acc i => mod (mul acc (body i)) p

end Term

/-- Compute the meaning of a term: resolve variables by their concrete offsets. -/
syntax "term_simp" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| term_simp) => `(tactic| simp [Term.denote_lvl, Nat.add_assoc,
      Nat.add_sub_cancel_left, Nat.add_sub_add_left])
  | `(tactic| term_simp [$xs,*]) => `(tactic| simp [Term.denote_lvl, Nat.add_assoc,
      Nat.add_sub_cancel_left, Nat.add_sub_add_left, $xs,*])

end Cslib.Complexity.NtimeDspace.ProgTerm
