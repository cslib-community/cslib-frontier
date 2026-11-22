/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.CounterLocal
public import Mathlib.RingTheory.PowerSeries.WellKnown

/-!
# The grouped inner loop as terms

Terms for the value of one constraint's multilinear extension at incidence
values, and for the product over the constraints of one group. Accessors are
term functions with residue-level contracts in every extension of the
environment.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.ProgTerm

open Term

variable {w : List Bool}

/-- A term function implements `F` at the residue level in every extension of `env`. -/
def ImplZ (w : List Bool) (env : List ℕ) (P : ℕ) (f : Term → Term) (F : ℕ → ZMod P) : Prop :=
  ∀ (pre : List ℕ) (a : Term), StableAt w a (pre ++ env) →
    ((f a).denote w (pre ++ env) : ZMod P) = F (a.denote w (pre ++ env))

theorem ImplZ.extend {env : List ℕ} {P : ℕ} {f : Term → Term} {F : ℕ → ZMod P}
    (h : ImplZ w env P f F) (pre : List ℕ) : ImplZ w (pre ++ env) P f F :=
  fun pre' a ha => by rw [← List.append_assoc] at ha ⊢; exact h (pre' ++ pre) a ha

/-- `1 - v` modulo `p`, for any natural `v`. -/
def oneSubT (p v : Term) : Term := sub (add p (const 1)) (mod v p)

theorem oneSubT_cast (p v : Term) (env : List ℕ) (P : ℕ) (hP0 : 0 < P)
    (hpv : p.denote w env = P) :
    ((oneSubT p v).denote w env : ZMod P) = 1 - (v.denote w env : ZMod P) := by
  have hP : v.denote w env % P ≤ P + 1 := (Nat.mod_lt _ hP0).le.trans (Nat.le_succ P)
  simp only [oneSubT, denote_sub, denote_add, denote_mod, denote_const, hpv]
  rw [Nat.cast_sub hP, ZMod.natCast_mod]
  push_cast
  simp

/-- The value of a constraint's extension: `∑_{A < 2^ar} W(A) ∏_{i<ar} (A_i ? V_i : 1 - V_i)`. -/
def clauseValueT (p ar : Term) (weight value : Term → Term) : Term :=
  Term.sumMod p (pow2 ar) fun A => mod (mul (weight A) (Term.prodMod p ar fun i =>
    ite (bit A i) (value i) (oneSubT p (value i)))) p

/-- A two-argument term function implements `F` at the residue level. -/
def ImplZ2 (w : List Bool) (env : List ℕ) (P : ℕ) (f : Term → Term → Term)
    (F : ℕ → ℕ → ZMod P) : Prop :=
  ∀ (pre : List ℕ) (a b : Term), StableAt w a (pre ++ env) → StableAt w b (pre ++ env) →
    ((f a b).denote w (pre ++ env) : ZMod P) = F (a.denote w (pre ++ env)) (b.denote w (pre ++ env))

/-- A three-argument term function implements `F` at the residue level. -/
def ImplZ3 (w : List Bool) (env : List ℕ) (P : ℕ) (f : Term → Term → Term → Term)
    (F : ℕ → ℕ → ℕ → ZMod P) : Prop :=
  ∀ (pre : List ℕ) (a b c : Term), StableAt w a (pre ++ env) → StableAt w b (pre ++ env) →
    StableAt w c (pre ++ env) →
    ((f a b c).denote w (pre ++ env) : ZMod P) =
      F (a.denote w (pre ++ env)) (b.denote w (pre ++ env)) (c.denote w (pre ++ env))

/-- A term function implements `F` exactly (with stable results) in every extension. -/
def ImplN (w : List Bool) (env : List ℕ) (f : Term → Term) (F : ℕ → ℕ) : Prop :=
  ∀ (pre : List ℕ) (a : Term), StableAt w a (pre ++ env) →
    (f a).denote w (pre ++ env) = F (a.denote w (pre ++ env)) ∧ StableAt w (f a) (pre ++ env)

/-- The product over the constraints of `group` of their extension values. -/
def groupValueT (p m : Term) (cGroup arity : Term → Term) (group : Term)
    (weight value : Term → Term → Term) : Term :=
  Term.prodMod p m fun e => ite (eqT (cGroup e) group)
    (clauseValueT p (arity e) (weight e) (value e)) (const 1)

/-- `1` if every test `i < n` gives `1`, for `0/1`-valued tests. -/
def allT (n : Term) (test : Term → Term) : Term :=
  eqT (sumT n fun i => sub (const 1) (test i)) (const 0)

theorem allT_denote (n : Term) (test : Term → Term) (env : List ℕ) (Pr : ℕ → Prop)
    [DecidablePred Pr]
    (ht : ∀ acc i, (test (lvl env.length)).denote w (acc :: i :: env) = if Pr i then 1 else 0) :
    (allT n test).denote w env = if ∀ i < n.denote w env, Pr i then 1 else 0 := by
  rw [allT, denote_eqT, denote_sumT _ _ env (fun i => if Pr i then 0 else 1) (fun acc i => by
    simp only [denote_sub, denote_const, ht]; split_ifs <;> rfl), denote_const]
  by_cases hall : ∀ i < n.denote w env, Pr i
  · rw [ite_eq_left hall, ite_eq_left (Finset.sum_eq_zero fun i
      hi => ite_eq_left (hall i (Finset.mem_range.mp hi)))]
  · rw [ite_eq_right hall, ite_eq_right]
    push Not at hall
    obtain ⟨i, hi, hni⟩ := hall
    intro hzero
    have := (Finset.sum_eq_zero_iff.mp hzero) i (Finset.mem_range.mpr hi)
    simp [hni] at this

/-- A two-argument term function implements `F` exactly, with stable results. -/
def ImplN2 (w : List Bool) (env : List ℕ) (f : Term → Term → Term) (F : ℕ → ℕ → ℕ) : Prop :=
  ∀ (pre : List ℕ) (a b : Term), StableAt w a (pre ++ env) → StableAt w b (pre ++ env) →
    (f a b).denote w (pre ++ env) = F (a.denote w (pre ++ env)) (b.denote w (pre ++ env)) ∧
      StableAt w (f a b) (pre ++ env)

theorem ImplN.extend {env : List ℕ} {f : Term → Term} {F : ℕ → ℕ} (h : ImplN w env f F)
    (pre : List ℕ) : ImplN w (pre ++ env) f F :=
  fun pre' a ha => by rw [← List.append_assoc] at ha ⊢; exact h (pre' ++ pre) a ha

theorem ImplN2.extend {env : List ℕ} {f : Term → Term → Term} {F : ℕ → ℕ → ℕ}
    (h : ImplN2 w env f F) (pre : List ℕ) : ImplN2 w (pre ++ env) f F :=
  fun pre' a b ha hb => by
    rw [← List.append_assoc] at ha hb ⊢; exact h (pre' ++ pre) a b ha hb

theorem ImplN2.fix {env : List ℕ} {f : Term → Term → Term} {F : ℕ → ℕ → ℕ}
    (h : ImplN2 w env f F) (a : Term) (ha : StableAt w a env) :
    ImplN w env (f a) (F (a.denote w env)) :=
  fun pre b hb => by
    have := h pre a b (ha.extend pre) hb
    rw [ha pre] at this
    exact this

theorem ImplZ3.fix2 {env : List ℕ} {P : ℕ} {f : Term → Term → Term → Term}
    {F : ℕ → ℕ → ℕ → ZMod P} (h : ImplZ3 w env P f F) (a b : Term) (ha : StableAt w a env)
    (hb : StableAt w b env) : ImplZ w env P (f a b) (F (a.denote w env) (b.denote w env)) :=
  fun pre c hc => by
    have := h pre a b c (ha.extend pre) (hb.extend pre) hc
    rw [ha pre, hb pre] at this
    exact this

theorem ImplZ3.extend {env : List ℕ} {P : ℕ} {f : Term → Term → Term → Term}
    {F : ℕ → ℕ → ℕ → ZMod P} (h : ImplZ3 w env P f F) (pre : List ℕ) :
    ImplZ3 w (pre ++ env) P f F :=
  fun pre' a b c ha hb hc => by
    rw [← List.append_assoc] at ha hb hc ⊢; exact h (pre' ++ pre) a b c ha hb hc

theorem ImplZ2.extend {env : List ℕ} {P : ℕ} {f : Term → Term → Term} {F : ℕ → ℕ → ZMod P}
    (h : ImplZ2 w env P f F) (pre : List ℕ) : ImplZ2 w (pre ++ env) P f F :=
  fun pre' a b ha hb => by
    rw [← List.append_assoc] at ha hb ⊢; exact h (pre' ++ pre) a b ha hb

/-- The bit of the local assignment `mask` at variable `v`: bit `rank v` of `mask`. -/
def assignBitT (n : Term) (gOf : Term → Term) (group mask v : Term) : Term :=
  bit mask (countBeforeT n gOf group v)

/-- The support test: every support variable of `group` is set by `mask`. -/
def supportTestT (n : Term) (gOf : Term → Term) (group : Term) (sBit : Term → Term)
    (mask : Term) : Term :=
  allT n fun v => sub (const 1) (mul (eqT (gOf v) group)
    (mul (sBit v) (sub (const 1) (assignBitT n gOf group mask v))))

section Support

variable {base : List ℕ} {n : ℕ} {Group : Type*} [DecidableEq Group]
  (groupOf : Fin n → Group) (code : Group → ℕ) (code_injective : Function.Injective code)
  (gOf : Term → Term) (G : ℕ → ℕ) (hG : ImplN w base gOf G)
  (hGcode : ∀ i (h : i < n), G i = code (groupOf ⟨i, h⟩))

/-- `∑_{v<n, v ∈ group} coef(v) · bit(v)`. -/
def measSumT (nT : Term) (gOf : Term → Term) (group : Term) (coef : Term → Term) (mask : Term) :
    Term :=
  sumT nT fun v => mul (eqT (gOf v) group) (mul (coef v) (assignBitT nT gOf group mask v))

/-- The measurement test: for every row `ρ`, `pos(ρ) + D = digit(ρ) + neg(ρ)`. -/
def measTestT (rows nT : Term) (gOf : Term → Term) (group : Term) (posC negC : Term → Term → Term)
    (tdig : Term → Term) (D mask : Term) : Term :=
  allT rows fun ρ => eqT (add (measSumT nT gOf group (posC ρ) mask) D)
    (add (tdig ρ) (measSumT nT gOf group (negC ρ) mask))

/-- The linear value: `∑_{v ∈ group} localC(v) · bit(v) + measTerm`, modulo `p`. -/
def linearValueT (p nT : Term) (gOf : Term → Term) (group : Term) (localC : Term → Term)
    (mask measTerm : Term) : Term :=
  mod (add (Term.sumMod p nT fun v => mul (eqT (gOf v) group)
    (mul (localC v) (assignBitT nT gOf group mask v))) measTerm) p

/-- The value of incidence `(e, i)` under the local assignment `mask`. -/
def incValueT (p nT : Term) (gOf : Term → Term) (group : Term)
    (localC : Term → Term → Term → Term) (measTerm corr : Term → Term → Term) (mask e i : Term) :
    Term :=
  mod (add (linearValueT p nT gOf group (localC e i) mask (measTerm e i)) (corr e i)) p

/-- The sum over local assignments of one group. -/
def sumGroupT (p nT : Term) (gOf : Term → Term) (group : Term) (sBit : Term → Term)
    (rows : Term) (posC negC : Term → Term → Term) (tdig : Term → Term) (D m : Term)
    (cGroup arity : Term → Term) (weight : Term → Term → Term)
    (localC : Term → Term → Term → Term) (measTerm corr : Term → Term → Term) : Term :=
  Term.sumMod p (pow2 (countBeforeT nT gOf group nT)) fun mask =>
    ite (mul (measTestT rows nT gOf group posC negC tdig D mask)
        (supportTestT nT gOf group sBit mask))
      (groupValueT p m cGroup arity group weight
        (incValueT p nT gOf group localC measTerm corr mask)) (const 0)

end Support

end Cslib.Complexity.NtimeDspace.ProgTerm
