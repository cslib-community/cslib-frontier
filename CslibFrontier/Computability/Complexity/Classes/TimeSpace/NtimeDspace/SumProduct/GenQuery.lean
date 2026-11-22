/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.SumProduct.Gen
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.SumProduct.PathTerm

/-!
# Explicit queries for a generated recursion

A generator given by closed programs (`GenProg`) yields the closed query programs of the
evaluator (`GenProg.queries`): each folds the child program along the path code, then reads the
node data of the state reached, reporting a leaf `0` past the fuel.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.SumProduct

open NtimeDspace.ProgLang NtimeDspace.ProgTerm Term NatList _root_.Turing.MultiTapeTM

theorem Prog'.closed_mono : ∀ (p : Prog) {m n : ℕ}, Prog'.closed m p = true → m ≤ n →
    Prog'.closed n p = true
  | .const _, _, _, _, _ => rfl
  | .var i, m, n, h, hmn => by
    simp only [Prog'.closed, decide_eq_true_eq] at h ⊢; omega
  | .add a b, m, n, h, hmn | .sub a b, m, n, h, hmn | .mul a b, m, n, h, hmn
  | .div a b, m, n, h, hmn | .mod a b, m, n, h, hmn | .bit a b, m, n, h, hmn
  | .lt a b, m, n, h, hmn => by
    simp only [Prog'.closed, Bool.and_eq_true] at h ⊢
    exact ⟨Prog'.closed_mono a h.1 hmn, Prog'.closed_mono b h.2 hmn⟩
  | .input a, m, n, h, hmn => by
    simp only [Prog'.closed] at h ⊢; exact Prog'.closed_mono a h hmn
  | .ite c t e, m, n, h, hmn => by
    simp only [Prog'.closed, Bool.and_eq_true] at h ⊢
    exact ⟨⟨Prog'.closed_mono c h.1.1 hmn, Prog'.closed_mono t h.1.2 hmn⟩,
      Prog'.closed_mono e h.2 hmn⟩
  | .letIn a b, m, n, h, hmn => by
    simp only [Prog'.closed, Bool.and_eq_true] at h ⊢
    exact ⟨Prog'.closed_mono a h.1 hmn, Prog'.closed_mono b h.2 (by omega)⟩
  | .fold k i b, m, n, h, hmn => by
    simp only [Prog'.closed, Bool.and_eq_true] at h ⊢
    exact ⟨⟨Prog'.closed_mono k h.1.1 hmn, Prog'.closed_mono i h.1.2 hmn⟩,
      Prog'.closed_mono b h.2 (by omega)⟩

/-- A generator given by closed programs: the initial state and the fuel from the length
`[len]`, the child state from `[state, symbol, len]`, the node data from `[state, len]`, and
the leaf bits from `[k, state, len]`. -/
structure GenProg where
  init : Prog
  fuel : Prog
  child : Prog
  tag : Prog
  prec : Prog
  param : Prog
  bit : Prog
  init_closed : Prog'.closed 1 init = true
  fuel_closed : Prog'.closed 1 fuel = true
  child_closed : Prog'.closed 3 child = true
  tag_closed : Prog'.closed 2 tag = true
  prec_closed : Prog'.closed 2 prec = true
  param_closed : Prog'.closed 2 param = true
  bit_closed : Prog'.closed 3 bit = true

namespace GenProg

variable (G : GenProg) (w : List Bool) (n : ℕ)

/-- The numeric generator at an input. -/
def toFun : GenFun where
  tag st := G.tag.eval w [st, n]
  prec st := G.prec.eval w [st, n]
  param st := G.param.eval w [st, n]
  bit st k := decide (0 < G.bit.eval w [k, st, n])
  child st i := G.child.eval w [st, i, n]

/-- The initial state. -/
def init₀ : ℕ := G.init.eval w [n]

/-- The fuel. -/
def fuel₀ : ℕ := G.fuel.eval w [n]

/-- The generated recursion. -/
def tree : SPTree := (G.toFun w n).tree (G.fuel₀ w n) (G.init₀ w n)

theorem stateAtF_eq (π : List ℕ) :
    stateAtF (childFun G.child w n) (G.init₀ w n) π = (G.toFun w n).stateAt (G.init₀ w n) π := by
  induction π with
  | nil => rfl
  | cons i π ih => simp only [stateAtF, GenFun.stateAt, ih]; rfl

/-! ### The query terms -/

/-- The state of the path `p` (a variable), from the length `l`. -/
def stateT (p l : Term) : Term :=
  letT (callT1 G.init l) fun s₀ => pathStateT G.child s₀ p l

/-- The tag query, as a term over `[path, len]`. -/
def tagT : Term :=
  letT (stateT G (lvl 1) (lvl 0)) fun st => letT (lengthT (lvl 1)) fun m =>
    letT (callT1 G.fuel (lvl 0)) fun H => letT (callT2 G.tag st (lvl 0)) fun t =>
      ite (lt m H) (ite (lt t (const 4)) (ite (lt (const 0) t) t (const 0)) (const 0)) (const 0)

/-- The precision query. -/
def precT : Term :=
  letT (stateT G (lvl 1) (lvl 0)) fun st => letT (lengthT (lvl 1)) fun m =>
    letT (callT1 G.fuel (lvl 0)) fun H =>
      ite (lt m H) (callT2 G.prec st (lvl 0)) (const 0)

/-- The parameter query. -/
def paramT : Term :=
  letT (stateT G (lvl 1) (lvl 0)) fun st => letT (lengthT (lvl 1)) fun m =>
    letT (callT1 G.fuel (lvl 0)) fun H => letT (callT2 G.tag st (lvl 0)) fun t =>
      ite (lt m H)
        (ite (lt t (const 4)) (ite (lt (const 0) t)
          (ite (lt t (const 2)) (callT2 G.param st (lvl 0))
            (ite (lt (const 2) t) (callT2 G.param st (lvl 0)) (const 0))) (const 0)) (const 0))
        (const 0)

/-- The leaf-bit query, as a term over `[k, path, len]`. -/
def bitT : Term :=
  letT (stateT G (lvl 1) (lvl 0)) fun st => callT3 G.bit (lvl 2) st (lvl 0)

theorem closed_two_add {q : Prog} {m : ℕ} (h : Prog'.closed m q = true) (k : ℕ) :
    Prog'.closed (k + m) q = true := Prog'.closed_mono q h (by omega)

theorem tagT_closed : Prog'.closed 2 (G.tagT 2) = true := by
  simp [tagT, stateT, pathStateT, lengthT, dropT, getT, tlT, hdT, tOnesT, callT1, callT2, callT3,
    Term.letT, Term.foldT, Term.ite, Term.lt, Term.lvl, Term.const, Term.add, Term.sub, Term.div,
    Term.mod, Term.bit, Term.mul, pow2, Prog'.closed, closed_two_add G.tag_closed, closed_two_add
        G.init_closed,
    closed_two_add G.child_closed, closed_two_add G.fuel_closed]

theorem precT_closed : Prog'.closed 2 (G.precT 2) = true := by
  simp [tagT, precT, paramT, bitT, stateT, pathStateT, lengthT, dropT, getT, tlT, hdT, tOnesT,
      callT1, callT2, callT3,
    Term.letT, Term.foldT, Term.ite, Term.lt, Term.lvl, Term.const, Term.add, Term.sub, Term.div,
    Term.mod, Term.bit, Term.mul, pow2, Prog'.closed, closed_two_add G.tag_closed, closed_two_add
        G.init_closed,
    closed_two_add G.child_closed, closed_two_add G.fuel_closed, closed_two_add G.prec_closed,
    closed_two_add G.param_closed, closed_two_add G.bit_closed]

theorem paramT_closed : Prog'.closed 2 (G.paramT 2) = true := by
  simp [tagT, precT, paramT, bitT, stateT, pathStateT, lengthT, dropT, getT, tlT, hdT, tOnesT,
      callT1, callT2, callT3,
    Term.letT, Term.foldT, Term.ite, Term.lt, Term.lvl, Term.const, Term.add, Term.sub, Term.div,
    Term.mod, Term.bit, Term.mul, pow2, Prog'.closed, closed_two_add G.tag_closed, closed_two_add
        G.init_closed,
    closed_two_add G.child_closed, closed_two_add G.fuel_closed, closed_two_add G.prec_closed,
    closed_two_add G.param_closed, closed_two_add G.bit_closed]

theorem bitT_closed : Prog'.closed 3 (G.bitT 3) = true := by
  simp [tagT, precT, paramT, bitT, stateT, pathStateT, lengthT, dropT, getT, tlT, hdT, tOnesT,
      callT1, callT2, callT3,
    Term.letT, Term.foldT, Term.ite, Term.lt, Term.lvl, Term.const, Term.add, Term.sub, Term.div,
    Term.mod, Term.bit, Term.mul, pow2, Prog'.closed, closed_two_add G.tag_closed, closed_two_add
        G.init_closed,
    closed_two_add G.child_closed, closed_two_add G.fuel_closed, closed_two_add G.prec_closed,
    closed_two_add G.param_closed, closed_two_add G.bit_closed]

/-- The explicit queries of the generated recursion. -/
def queries : Queries where
  tag := G.tagT 2
  prec := G.precT 2
  param := G.paramT 2
  bit := G.bitT 3
  tag_closed := G.tagT_closed
  prec_closed := G.precT_closed
  param_closed := G.paramT_closed
  bit_closed := G.bitT_closed

variable {w} {B : ℕ}

theorem denote_stateT {a b : ℕ} {env : List ℕ} (ha : a < env.length) (hb : b < env.length) :
    (G.stateT (lvl a) (lvl b)).denote w env =
      pathStateF (childFun G.child w ((lvl b).denote w env)) (G.init.eval w [(lvl b).denote w env])
        ((lvl a).denote w env) := by
  rw [stateT, denote_letT, denote_pathStateT G.child_closed (by simp) (by lvl_disch) (by lvl_disch),
    denote_lvl_let, lvl_cons ha, lvl_cons hb, denote_callT1 G.init_closed hb]

/-- The state of a path, from its code. -/
theorem state_enc (π : List ℕ) :
    pathStateF (childFun G.child w n) (G.init.eval w [n]) (enc π) =
      (G.toFun w n).stateAt (G.init₀ w n) π := by
  rw [pathStateF_enc]; exact G.stateAtF_eq w n π

theorem lvl0_one (m : ℕ) : (lvl 0).denote w [m] = m := rfl
theorem lvl1_two (x m : ℕ) : (lvl 1).denote w [x, m] = x := rfl
theorem lvl0_two (x m : ℕ) : (lvl 0).denote w [x, m] = m := rfl
theorem lvl2_three (k x m : ℕ) : (lvl 2).denote w [k, x, m] = k := rfl
theorem lvl1_three (k x m : ℕ) : (lvl 1).denote w [k, x, m] = x := rfl
theorem lvl0_three (k x m : ℕ) : (lvl 0).denote w [k, x, m] = m := rfl

theorem tag_aux (t : ℕ) : (if t < 4 then (if 0 < t then t else 0) else 0) =
    (if t = 1 ∨ t = 2 ∨ t = 3 then t else 0) := by
  split_ifs <;> omega

theorem param_aux (t q : ℕ) : (if t < 4 then (if 0 < t then (if t < 2 then q else
    (if 2 < t then q else 0)) else 0) else 0) = (if t = 1 ∨ t = 3 then q else 0) := by
  split_ifs <;> first | rfl | omega

theorem queries_tag (π : List ℕ) :
    G.queries.tag.eval w [enc π, n] = ((G.toFun w n).genQ (G.fuel₀ w n) (G.init₀ w n) π).tag := by
  show (G.tagT).denote w [enc π, n] = _
  simp (disch := lvl_disch) only [tagT, denote_letT, G.denote_stateT, denote_lengthT,
    denote_callT1 G.fuel_closed, denote_callT2 G.tag_closed, denote_ite_lt, denote_const,
    lvl_cons, denote_lvl_let, lvl1_two, lvl0_two, lvl0_one, G.state_enc, lengthF_enc]
  by_cases hlt : π.length < G.fuel.eval w [n]
  · simp only [GenFun.genQ, fuel₀, hlt, if_true]
    exact tag_aux _
  · simp only [GenFun.genQ, fuel₀, hlt, if_false]

theorem queries_prec (π : List ℕ) :
    G.queries.prec.eval w [enc π, n] = ((G.toFun w n).genQ (G.fuel₀ w n) (G.init₀ w n) π).prec := by
  show (G.precT).denote w [enc π, n] = _
  simp (disch := lvl_disch) only [precT, denote_letT, G.denote_stateT, denote_lengthT,
    denote_callT1 G.fuel_closed, denote_callT2 G.prec_closed, denote_ite_lt, denote_const,
    lvl_cons, denote_lvl_let, lvl1_two, lvl0_two, lvl0_one, G.state_enc, lengthF_enc]
  by_cases hlt : π.length < G.fuel.eval w [n]
  · simp only [GenFun.genQ, fuel₀, hlt, if_true, toFun]
  · simp only [GenFun.genQ, fuel₀, hlt, if_false]

theorem queries_param (π : List ℕ) :
    G.queries.param.eval w [enc π, n] =
      ((G.toFun w n).genQ (G.fuel₀ w n) (G.init₀ w n) π).param := by
  show (G.paramT).denote w [enc π, n] = _
  simp (disch := lvl_disch) only [paramT, denote_letT, G.denote_stateT, denote_lengthT,
    denote_callT1 G.fuel_closed, denote_callT2 G.tag_closed, denote_callT2 G.param_closed,
    denote_ite_lt, denote_const, lvl_cons, denote_lvl_let, lvl1_two, lvl0_two, lvl0_one,
        G.state_enc,
    lengthF_enc]
  by_cases hlt : π.length < G.fuel.eval w [n]
  · simp only [GenFun.genQ, fuel₀, hlt, if_true]
    exact param_aux _ _
  · simp only [GenFun.genQ, fuel₀, hlt, if_false]

theorem queries_bit (k : ℕ) (π : List ℕ) :
    (0 < G.queries.bit.eval w [k, enc π, n]) ↔
      (G.toFun w n).genLB (G.init₀ w n) π k = true := by
  show (0 < (G.bitT).denote w [k, enc π, n]) ↔ _
  simp (disch := lvl_disch) only [bitT, denote_letT, G.denote_stateT, denote_callT3 G.bit_closed,
    lvl_cons, denote_lvl_let, lvl2_three, lvl1_three, lvl0_three, lvl0_one, G.state_enc]
  simp only [lvl1_two, G.state_enc]
  simp [GenFun.genLB, toFun, init₀]

/-- The value bounds a path needs: its code, and the component programs at the states along it. -/
structure PathBounded (B : ℕ) (π : List ℕ) : Prop where
  code : max (enc π) 8 + 1 ≤ B
  init : G.init.Bounded w B [n]
  fuel : G.fuel.Bounded w B [n]
  child : ∀ j < π.length, G.child.Bounded w B
    [(G.toFun w n).stateAt (G.init₀ w n) (π.drop (j + 1)), π[j]!, n]
  tag : G.tag.Bounded w B [(G.toFun w n).stateAt (G.init₀ w n) π, n]
  prec : G.prec.Bounded w B [(G.toFun w n).stateAt (G.init₀ w n) π, n]
  param : G.param.Bounded w B [(G.toFun w n).stateAt (G.init₀ w n) π, n]

variable {G n}

theorem bnd_stateT {B : ℕ} {π : List ℕ} (h : G.PathBounded (w := w) n B π) :
    (G.stateT (lvl 1) (lvl 0)).Bnd w B [enc π, n] := by
  rw [stateT, bnd_letT]
  refine ⟨bnd_callT1 G.init_closed (by simp) (by rw [lvl0_two]; exact h.init), ?_⟩
  refine bnd_pathStateT G.child_closed (by simp) (by simp) (by simp)
    (by rw [lvl_cons (by simp), lvl1_two]) h.code fun j hj => ?_
  simp (disch := lvl_disch) only [lvl_cons, lvl0_two, lvl0_one, denote_lvl_let, denote_callT1
      G.init_closed]
  have := h.child j hj
  rw [← G.stateAtF_eq] at this
  exact this

theorem bnd_queries_tag {B : ℕ} {π : List ℕ} (h : G.PathBounded (w := w) n B π) (h4 : 4 ≤ B) :
    G.queries.tag.Bounded w B [enc π, n] := by
  show (G.tagT).Bnd w B [enc π, n]
  rw [tagT, bnd_letT]
  refine ⟨bnd_stateT h, ?_⟩
  rw [bnd_letT]
  refine ⟨bnd_lengthT (by simp) (by rw [lvl_cons (by simp), lvl1_two]) h.code, ?_⟩
  rw [bnd_letT]
  refine ⟨bnd_callT1 G.fuel_closed (by simp) (by
    simp (disch := lvl_disch) only [lvl_cons, lvl0_two, lvl0_one]; exact h.fuel), ?_⟩
  rw [bnd_letT]
  refine ⟨bnd_callT2 G.tag_closed (by simp) (by simp) (by
    simp (disch := lvl_disch) only [lvl_cons, lvl0_two, lvl0_one, denote_lvl_let, G.denote_stateT,
        lvl1_two,
      G.state_enc]
    exact h.tag), ?_⟩
  refine bnd_ite_of (by simp) (bnd_ite_of (by simp; omega) (bnd_ite_of (by simp) trivial
    (by simp)) (by simp)) (by simp)

theorem bnd_queries_prec {B : ℕ} {π : List ℕ} (h : G.PathBounded (w := w) n B π) (h4 : 4 ≤ B) :
    G.queries.prec.Bounded w B [enc π, n] := by
  show (G.precT).Bnd w B [enc π, n]
  rw [precT, bnd_letT]
  refine ⟨bnd_stateT h, ?_⟩
  rw [bnd_letT]
  refine ⟨bnd_lengthT (by simp) (by rw [lvl_cons (by simp), lvl1_two]) h.code, ?_⟩
  rw [bnd_letT]
  refine ⟨bnd_callT1 G.fuel_closed (by simp) (by
    simp (disch := lvl_disch) only [lvl_cons, lvl0_two, lvl0_one]; exact h.fuel), ?_⟩
  refine bnd_ite_of (by simp) (bnd_callT2 G.prec_closed (by simp) (by simp) (by
    simp (disch := lvl_disch) only [lvl_cons, lvl0_two, lvl0_one, denote_lvl_let, G.denote_stateT,
        lvl1_two,
      G.state_enc]
    exact h.prec)) (by simp)

theorem bnd_queries_param {B : ℕ} {π : List ℕ} (h : G.PathBounded (w := w) n B π) (h4 : 4 ≤ B) :
    G.queries.param.Bounded w B [enc π, n] := by
  show (G.paramT).Bnd w B [enc π, n]
  rw [paramT, bnd_letT]
  refine ⟨bnd_stateT h, ?_⟩
  rw [bnd_letT]
  refine ⟨bnd_lengthT (by simp) (by rw [lvl_cons (by simp), lvl1_two]) h.code, ?_⟩
  rw [bnd_letT]
  refine ⟨bnd_callT1 G.fuel_closed (by simp) (by
    simp (disch := lvl_disch) only [lvl_cons, lvl0_two, lvl0_one]; exact h.fuel), ?_⟩
  rw [bnd_letT]
  refine ⟨bnd_callT2 G.tag_closed (by simp) (by simp) (by
    simp (disch := lvl_disch) only [lvl_cons, lvl0_two, lvl0_one, denote_lvl_let, G.denote_stateT,
        lvl1_two,
      G.state_enc]
    exact h.tag), ?_⟩
  refine bnd_ite_of (by simp) (bnd_ite_of (by simp; omega) (bnd_ite_of (by simp)
    (bnd_ite_of (by simp; omega) ?_ (bnd_ite_of (by simp; omega) ?_ (by simp))) (by simp))
    (by simp)) (by simp)
  all_goals exact bnd_callT2 G.param_closed (by simp) (by simp) (by
    simp (disch := lvl_disch) only [lvl_cons, lvl0_two, lvl0_one, denote_lvl_let, G.denote_stateT,
        lvl1_two,
      G.state_enc]
    exact h.param)

theorem bnd_queries_bit {B k : ℕ} {π : List ℕ} (h : G.PathBounded (w := w) n B π)
    (hb : G.bit.Bounded w B [k, (G.toFun w n).stateAt (G.init₀ w n) π, n]) :
    G.queries.bit.Bounded w B [k, enc π, n] := by
  show (G.bitT).Bnd w B [k, enc π, n]
  rw [bitT, bnd_letT]
  refine ⟨?_, ?_⟩
  · rw [stateT, bnd_letT]
    refine ⟨bnd_callT1 G.init_closed (by simp) (by
      simp (disch := lvl_disch) only [lvl_cons, lvl0_one]; exact h.init), ?_⟩
    refine bnd_pathStateT G.child_closed (by simp) (by simp) (by simp)
      (by simp (disch := lvl_disch) only [lvl_cons, lvl1_two]) h.code fun j hj => ?_
    simp (disch := lvl_disch) only [lvl_cons, lvl0_one, denote_lvl_let, denote_callT1 G.init_closed]
    have := h.child j hj
    rw [← G.stateAtF_eq] at this
    exact this
  · refine bnd_callT3 G.bit_closed (by simp) (by simp) (by simp) ?_
    simp (disch := lvl_disch) only [lvl_cons, lvl0_one, lvl1_two, lvl2_three, denote_lvl_let,
      G.denote_stateT, G.state_enc]
    exact hb

end GenProg

open SPTree in
/-- **Proposition 3.2 for generated recursions.** A sum–product recursion generated by closed
programs
is evaluated bitwise in time `2^(C·X)` and space `C·X`. -/
theorem gen_decidable {α : Type} {encA : α ↪ List Bool} (G : GenProg) (k0 : α → ℕ)
    (rootP XP : Prog) (hroot : Prog'.closed 1 rootP = true) (hXP : Prog'.closed 1 XP = true)
    (ℓ V X : α → ℕ) (hℓ : ∀ a, 1 ≤ ℓ a)
    (hprec : ∀ a, (G.tree (encA a) (encA a).length).PrecLe (2 ^ ℓ a))
    (hV : ∀ a π, Valid (G.tree (encA a) (encA a).length) π →
      (node (G.tree (encA a) (encA a).length) π).prec +
        (node (G.tree (encA a) (encA a).length) π).param ≤ V a)
    (hk0V : ∀ a, k0 a ≤ V a)
    (hXcost : ∀ a, 34 * (G.tree (encA a) (encA a).length).cost (ℓ a) + 2 * (V a).size + 16 ≤ X a)
    (hXlog : ∀ a, (encA a).length.log2 + 1 ≤ X a)
    (hrootv : ∀ a, rootP.eval (encA a) [(encA a).length] = k0 a ∧
      rootP.Bounded (encA a) (2 ^ (X a + 1)) [(encA a).length])
    (hXv : ∀ a, XP.eval (encA a) [(encA a).length] = X a ∧
      XP.Bounded (encA a) (2 ^ (X a + 1)) [(encA a).length])
    (hpath : ∀ a π, Valid (G.tree (encA a) (encA a).length) π →
      G.PathBounded (w := encA a) (encA a).length (2 ^ (X a + 1)) π)
    (hbit : ∀ a π k, Valid (G.tree (encA a) (encA a).length) π →
      (node (G.tree (encA a) (encA a).length) π).tag = 0 →
      k < (node (G.tree (encA a) (encA a).length) π).prec →
      G.bit.Bounded (encA a) (2 ^ (X a + 1))
        [k, (G.toFun (encA a) (encA a).length).stateAt (G.init₀ (encA a) (encA a).length) π,
          (encA a).length]) :
    ∃ C, DecidableInTimeAndSpace {a | (G.tree (encA a) (encA a).length).value.testBit (k0 a) = true}
      encA (fun a => 2 ^ (C * X a)) (fun a => C * X a) := by
  have h4 : ∀ a, 4 ≤ 2 ^ (X a + 1) := fun a => by
    have : 16 ≤ X a := by have := hXcost a; omega
    calc 4 = 2 ^ 2 := rfl
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)
  refine sumProduct_decidable (fun a => G.tree (encA a) (encA a).length) k0 G.queries rootP XP hroot
    hXP ℓ V X hℓ hprec hV hk0V hXcost hXlog hrootv hXv (fun a π hπ => ?_) (fun a π k hπ ht hk => ?_)
  · have hag := (GenFun.agrees_tree _ (G.fuel₀ (encA a) (encA a).length)
      (G.init₀ (encA a) (encA a).length) π hπ).1
    rw [List.append_nil] at hag
    have hp := hpath a π hπ
    refine ⟨?_, ?_, ?_, G.bnd_queries_tag hp (h4 a), G.bnd_queries_prec hp (h4 a),
      G.bnd_queries_param hp (h4 a)⟩
    · rw [G.queries_tag, hag]; rfl
    · rw [G.queries_prec, hag]; rfl
    · rw [G.queries_param, hag]; rfl
  · have hag := (GenFun.agrees_tree _ (G.fuel₀ (encA a) (encA a).length)
      (G.init₀ (encA a) (encA a).length) π hπ).2 k ht hk
    rw [List.append_nil] at hag
    refine ⟨?_, G.bnd_queries_bit (hpath a π hπ) (hbit a π k hπ ht hk)⟩
    rw [G.queries_bit, hag]
    rfl

end Cslib.Complexity.NtimeDspace.SumProduct
