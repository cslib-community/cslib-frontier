/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.NetSystemTerm

/-!
# Value bounds for the network accessors

For any arguments: the arity is at most the number of edges, a port is below
the square of the number of edges, and a table entry is at most `2^b` (a count
of coin strings of `b` bits, or a 0/1 test).
-/

public section

namespace Cslib.Complexity.NtimeDspace.LocalSim

open ProgTerm ProgTerm.Term _root_.Turing _root_.Turing.MultiTapePTM

variable {w : List Bool}

theorem eqT_le_one (a b : Term) (env : List ℕ) : (eqT a b).denote w env ≤ 1 := by
  rw [denote_eqT]; split_ifs <;> omega

theorem lt_le_one (a b : Term) (env : List ℕ) : (Term.lt a b).denote w env ≤ 1 := by
  rw [denote_lt]; split_ifs <;> omega

theorem mul_le_one {a b : Term} {env : List ℕ} (ha : a.denote w env ≤ 1) (hb : b.denote w env ≤ 1) :
    (mul a b).denote w env ≤ 1 := by
  rw [denote_mul]; nlinarith

theorem allT_le_one (n : Term) (f : Term → Term) (env : List ℕ) : (allT n f).denote w env ≤ 1 :=
  eqT_le_one _ _ _

theorem ite_le {c t e : Term} {env : List ℕ} {V : ℕ} (ht : t.denote w env ≤ V)
    (he : e.denote w env ≤ V) : (Term.ite c t e).denote w env ≤ V := by
  rw [denote_ite]; split_ifs <;> assumption

/-- A sum of terms each at most `M` is at most `count · M`. -/
theorem sumT_le (n : Term) (body : Term → Term) (env : List ℕ) (M : ℕ)
    (hb : ∀ acc j, j < n.denote w env → (body (lvl env.length)).denote w (acc :: j :: env) ≤ M) :
    (sumT n body).denote w env ≤ n.denote w env * M := by
  simp only [sumT, denote_foldT, denote_const]
  have key : ∀ m ≤ n.denote w env, foldAcc w (fun acc i => add acc (body i)) env 0 m ≤ m * M := by
    intro m hm
    induction m with
    | zero => simp
    | succ m ih =>
      rw [foldAcc_succ]
      simp only [denote_add, denote_lvl_acc]
      have := hb (foldAcc w (fun acc i => add acc (body i)) env 0 m) m (by omega)
      have := ih (by omega)
      rw [Nat.succ_mul]; omega
  exact key _ le_rfl

variable {k s : ℕ} {State : Type} [DecidableEq State] {machine : MultiTapePTM k Bool State}
  {e : State ≃ Fin s}

theorem arityNT_le (qT bT σT eT : Term) (env : List ℕ) :
    (arityNT k s qT bT σT eT).denote w env ≤ (edgesT k s qT bT).denote w env := by
  unfold arityNT portCountT
  have := sumT_le (w := w) (edgesT k s qT bT)
    (fun j => portPredT k qT (letterBitsT k s bT) σT eT j) env 1 (fun _ _ _ => lt_le_one _ _ _)
  simpa using this

theorem portAtT_le (qT bT σT eT iT : Term) (env : List ℕ) :
    (portAtT k s qT bT σT eT iT).denote w env ≤
      (edgesT k s qT bT).denote w env * (edgesT k s qT bT).denote w env := by
  unfold portAtT
  refine sumT_le _ _ env _ (fun acc j hj => ?_)
  simp only [denote_mul, denote_lvl_index]
  have hX : (portPredT k qT (letterBitsT k s bT) σT eT (lvl env.length)).denote w
      (acc :: j :: env) ≤ 1 :=
    lt_le_one _ _ _
  have hY := eqT_le_one (w := w) (portCountT k qT (letterBitsT k s bT) σT eT (lvl env.length)) iT
    (acc :: j :: env)
  have hXY : (portPredT k qT (letterBitsT k s bT) σT eT (lvl env.length)).denote w
      (acc :: j :: env) *
      (eqT (portCountT k qT (letterBitsT k s bT) σT eT (lvl env.length)) iT).denote w
          (acc :: j :: env) ≤ 1 := by
    nlinarith
  calc _ ≤ 1 * j := Nat.mul_le_mul_right _ hXY
    _ ≤ _ := by omega

theorem condT_le_one (bT JpT JmT stO trO : Term) (offO dC cellO : Term → Term) (R a : Term)
    (env : List ℕ) : (condT k bT JpT JmT stO trO offO dC cellO R a).denote w env ≤ 1 := by
  unfold condT
  exact mul_le_one (eqT_le_one _ _ _) (mul_le_one (eqT_le_one _ _ _) (mul_le_one
    (mul_le_one (lt_le_one _ _ _) (eqT_le_one _ _ _)) (mul_le_one (allT_le_one _ _ _)
      (allT_le_one _ _ _))))

omit [DecidableEq State] in
theorem intervalEntryT_le (RT NT qT bT σT : Term) (L : Term → Term) (iT : Term) (env : List ℕ) :
    (intervalEntryT (k := k) (s := s) e machine RT NT qT bT σT L iT).denote w env ≤
      2 ^ bT.denote w env := by
  unfold intervalEntryT
  apply ite_le
  · unfold intervalCountT
    apply le_trans (sumT_le _ _ env 1 ?_)
    · rw [denote_pow2, mul_one]
    · intro acc j _
      exact condT_le_one _ _ _ _ _ _ _ _ _ _ _
  · exact Nat.zero_le _

omit [DecidableEq State] in
theorem oldEntryT_le (RT NT qT bT σT : Term) (L : Term → Term) (vT : Term) (env : List ℕ) :
    (oldEntryT k s e machine RT NT qT bT σT L vT).denote w env ≤ 2 ^ bT.denote w env := by
  have h1 : 1 ≤ 2 ^ bT.denote w env := Nat.one_le_two_pow
  unfold oldEntryT
  exact ite_le (intervalEntryT_le _ _ _ _ _ _ _ _)
    (ite_le (le_trans (mul_le_one (lt_le_one _ _ _) (eqT_le_one _ _ _)) h1)
        (by rw [denote_const]; exact h1))

omit [DecidableEq State] in
theorem weightNT_le (RT NT qT bT σT eT A : Term) (env : List ℕ) :
    (weightNT k s e machine RT NT qT bT σT eT A).denote w env ≤ 2 ^ bT.denote w env := by
  have h1 : 1 ≤ 2 ^ bT.denote w env := Nat.one_le_two_pow
  unfold weightNT tableEntryT
  exact ite_le (ite_le (oldEntryT_le _ _ _ _ _ _ _ _) (by rw [denote_const]; exact Nat.zero_le _))
    ((eqT_le_one _ _ _).trans h1)

end Cslib.Complexity.NtimeDspace.LocalSim
