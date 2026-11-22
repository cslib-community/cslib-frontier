/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.LocalIntervalCount

/-!
# The explicit block network's graph as terms

Terms for Complexitylib's numeric description of the explicit block network:
digit counts of the schedule, windows, last and next appearances, edge
sources and targets, and the ports of a vertex with the position of a port.
Optional numbers are coded as `0` for `none` and `x + 1` for `some x`
(`optCode`). Each term is proved equal to the Complexitylib function.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.LocalSim

open ProgTerm ProgTerm.Term _root_.Turing _root_.Turing.MultiTapePTM

variable {w : List Bool}

/-! ### Searching -/

/-- `none` as `0`, `some x` as `x + 1`. -/
def optCode : Option ℕ → ℕ
  | none => 0
  | some x => x + 1

/-- The last `j < i` with `p j`, coded, by a left fold. -/
def lastNum (p : ℕ → Bool) (i : ℕ) : ℕ :=
  (List.range i).foldl (fun acc j => if p j then j + 1 else acc) 0

theorem lastNum_eq (p : ℕ → Bool) (i : ℕ) :
    lastNum p i = optCode
        (((List.range i).find? fun j => p (i - 1 - j)).map fun j => i - 1 - j) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have hfold : lastNum p (i + 1) = if p i then i + 1 else lastNum p i := by
      simp [lastNum, List.range_succ, List.foldl_append]
    rw [hfold, List.range_succ_eq_map, List.find?_cons]
    by_cases hp : p i
    · simp [hp, optCode]
    · simp only [hp, Nat.add_sub_cancel, Nat.sub_zero, ite_false, Bool.false_eq_true]
      rw [List.find?_map, ih]
      congr 1
      have h1 : ((fun x => p (i - x)) ∘ Nat.succ) = fun j => p (i - 1 - j) := by
        funext j; simp only [Function.comp]; congr 1; omega
      rw [h1, Option.map_map]
      congr 1
      funext j
      simp only [Function.comp]
      omega

/-- The first `j < n` with `p j`, coded, by a left fold. -/
def firstNum (p : ℕ → Bool) (n : ℕ) : ℕ :=
  (List.range n).foldl (fun acc j => if acc = 0 ∧ p j = true then j + 1 else acc) 0

theorem firstNum_eq (p : ℕ → Bool) (n : ℕ) : firstNum p n = optCode ((List.range n).find? p) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hfold : firstNum p (n + 1) =
        if firstNum p n = 0 ∧ p n = true then n + 1 else firstNum p n := by
      unfold firstNum; rw [List.range_succ, List.foldl_append]; rfl
    rw [hfold, ih, List.range_succ, List.find?_append]
    cases h : (List.range n).find? p with
    | none => by_cases hp : p n <;> simp [optCode, hp]
    | some x => simp [optCode]

/-! ### Digit counts and windows -/

/-- Indicator `a ≤ b`. -/
def leT' (a b : Term) : Term := sub (const 1) (lt b a)

@[simp] theorem denote_leT' (a b : Term) (env : List ℕ) :
    (leT' a b).denote w env = if a.denote w env ≤ b.denote w env then 1 else 0 := by
  simp only [leT', denote_sub, denote_const, denote_lt]
  split_ifs <;> omega

theorem StableAt.leT' {a b : Term} {env : List ℕ} (ha : StableAt w a env) (hb : StableAt w b env) :
    StableAt w (leT' a b) env := fun extra => by simp [ha extra, hb extra]

/-- The digit of `σ` at position `c + (k + 1) i'` in base `3`. -/
def sdigT (k : ℕ) (σT cT iT : Term) : Term :=
  mod (divPowT (const 3) σT (add cT (mul (const (k + 1)) iT))) (const 3)

theorem denote_sdigT (k : ℕ) (σT cT iT : Term) (env : List ℕ) :
    (sdigT k σT cT iT).denote w env =
      σT.denote w env / 3 ^ (cT.denote w env + (k + 1) * iT.denote w env) % 3 := by
  simp [sdigT, divPowT_denote _ _ _ _ (stableAt_const _ _)]

theorem StableAt.sdigT (k : ℕ) {σT cT iT : Term} {env : List ℕ} (h1 : StableAt w σT env)
    (h2 : StableAt w cT env) (h3 : StableAt w iT env) : StableAt w (sdigT k σT cT iT) env :=
  fun extra => by rw [denote_sdigT, denote_sdigT, h1 extra, h2 extra, h3 extra]

def digitCountT (k : ℕ) (σT cT δT iT : Term) : Term :=
  sumT iT fun i' => eqT (sdigT k σT cT i') δT

theorem denote_digitCountT (k : ℕ) {σT cT δT : Term} (iT : Term) {env : List ℕ}
    (h1 : StableAt w σT env) (h2 : StableAt w cT env) (h3 : StableAt w δT env) :
    (digitCountT k σT cT δT iT).denote w env =
      digitCount k (σT.denote w env) (cT.denote w env) (δT.denote w env) (iT.denote w env) := by
  unfold digitCountT digitCount
  rw [denote_sumT _ _ env (fun i' => if σT.denote w env / 3 ^ (cT.denote w env + (k + 1) * i') % 3
      = δT.denote w env then 1 else 0), countP_eq_sum]
  · simp
  · intro acc i'
    simp [denote_sdigT, h1.cons₂, h2.cons₂, h3.cons₂]

theorem StableAt.digitCountT (k : ℕ) {σT cT δT iT : Term} {env : List ℕ}
    (h1 : StableAt w σT env) (h2 : StableAt w cT env) (h3 : StableAt w δT env)
    (h4 : StableAt w iT env) : StableAt w (digitCountT k σT cT δT iT) env := fun extra => by
  rw [denote_digitCountT k iT (h1.extend extra) (h2.extend extra) (h3.extend extra),
    denote_digitCountT k iT h1 h2 h3, h1 extra, h2 extra, h3 extra, h4 extra]

def inWindowT (k : ℕ) (σT cT iT δT i'T : Term) : Term :=
  mul (leT' (add (add (digitCountT k σT cT (const 2) i'T) (digitCountT k σT cT (const 0) iT))
      (const 1))
    (add (add (add (digitCountT k σT cT (const 0) i'T) (digitCountT k σT cT (const 2) iT)) δT)
      (const 1)))
  (leT' (add (add (digitCountT k σT cT (const 0) i'T) (digitCountT k σT cT (const 2) iT)) δT)
    (add (add (digitCountT k σT cT (const 2) i'T) (digitCountT k σT cT (const 0) iT)) (const 2)))

theorem denote_inWindowT (k : ℕ) {σT cT : Term} (iT δT i'T : Term) {env : List ℕ}
    (h1 : StableAt w σT env) (h2 : StableAt w cT env) :
    (inWindowT k σT cT iT δT i'T).denote w env =
      if inWindowNum k (σT.denote w env) (cT.denote w env) (iT.denote w env) (δT.denote w env)
        (i'T.denote w env) then 1 else 0 := by
  unfold inWindowT inWindowNum
  simp only [denote_mul, denote_leT', denote_add, denote_const,
    denote_digitCountT k _ h1 h2 (stableAt_const _ _)]
  split_ifs <;> simp_all <;> omega

theorem StableAt.inWindowT (k : ℕ) {σT cT iT δT i'T : Term} {env : List ℕ}
    (h1 : StableAt w σT env) (h2 : StableAt w cT env) (h3 : StableAt w iT env)
    (h4 : StableAt w δT env) (h5 : StableAt w i'T env) :
    StableAt w (inWindowT k σT cT iT δT i'T) env := fun extra => by
  rw [denote_inWindowT k _ _ _ (h1.extend extra) (h2.extend extra),
    denote_inWindowT k _ _ _ h1 h2, h1 extra, h2 extra, h3 extra, h4 extra, h5 extra]

/-! ### Last and next appearances -/

def lastBeforeT (k : ℕ) (σT cT iT δT : Term) : Term :=
  foldT iT (const 0) fun acc j => ite (inWindowT k σT cT iT δT j) (add j (const 1)) acc

theorem denote_lastBeforeT (k : ℕ) {σT cT iT δT : Term} {env : List ℕ}
    (h1 : StableAt w σT env) (h2 : StableAt w cT env) (h3 : StableAt w iT env)
    (h4 : StableAt w δT env) :
    (lastBeforeT k σT cT iT δT).denote w env =
      optCode (lastBeforeNum k (σT.denote w env) (cT.denote w env) (iT.denote w env)
        (δT.denote w env)) := by
  unfold lastBeforeT lastBeforeNum
  rw [denote_foldT, denote_const, foldAcc_eq _ env (fun acc j => if inWindowNum k
      (σT.denote w env) (cT.denote w env) (iT.denote w env) (δT.denote w env) j then j + 1
      else acc)]
  · rw [show (List.range (iT.denote w env)).foldl _ 0 = lastNum _ _ from rfl, lastNum_eq]
  · intro acc j
    have hw := denote_inWindowT k iT δT (lvl env.length) (h1.extend [acc, j]) (h2.extend [acc, j])
    simp only [List.cons_append, List.nil_append] at hw
    rw [denote_ite, hw]
    simp only [h1.cons₂, h2.cons₂, h3.cons₂, h4.cons₂, denote_lvl_index, denote_lvl_acc,
      denote_add, denote_const]
    split_ifs <;> simp_all

def firstAfterT (k : ℕ) (qT σT cT iT δT : Term) : Term :=
  foldT qT (const 0) fun acc j =>
    ite (mul (eqT acc (const 0)) (mul (lt iT j) (inWindowT k σT cT iT δT j)))
      (add j (const 1)) acc

theorem denote_firstAfterT (k : ℕ) {qT σT cT iT δT : Term} {env : List ℕ}
    (h1 : StableAt w σT env) (h2 : StableAt w cT env) (h3 : StableAt w iT env)
    (h4 : StableAt w δT env) :
    (firstAfterT k qT σT cT iT δT).denote w env =
      optCode (firstAfterNum k (qT.denote w env) (σT.denote w env) (cT.denote w env)
        (iT.denote w env) (δT.denote w env)) := by
  unfold firstAfterT firstAfterNum
  rw [denote_foldT, denote_const, foldAcc_eq _ env (fun acc j =>
      if acc = 0 ∧ (decide (iT.denote w env < j) && inWindowNum k (σT.denote w env)
        (cT.denote w env) (iT.denote w env) (δT.denote w env) j) = true then j + 1 else acc)]
  · rw [show (List.range (qT.denote w env)).foldl _ 0 = firstNum _ _ from rfl, firstNum_eq]
  · intro acc j
    have hw := denote_inWindowT k iT δT (lvl env.length) (h1.extend [acc, j]) (h2.extend [acc, j])
    simp only [List.cons_append, List.nil_append] at hw
    rw [denote_ite, denote_mul, denote_mul, denote_lt, hw]
    simp only [h1.cons₂, h2.cons₂, h3.cons₂, h4.cons₂, denote_lvl_index, denote_lvl_acc,
      denote_add, denote_const, denote_eqT]
    by_cases ha : acc = 0 <;> by_cases hi : iT.denote w env < j <;>
      by_cases hw : inWindowNum k (σT.denote w env) (cT.denote w env) (iT.denote w env)
        (δT.denote w env) j <;> simp [ha, hi, hw]

end Cslib.Complexity.NtimeDspace.LocalSim
