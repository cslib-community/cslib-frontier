/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.InnerLoopTerm
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.LocalInterval
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.LocalStart

/-!
# The interval count term

`condT` evaluates `condN` (`denote_condT`), and `intervalCountT` sums it over
all coin strings. `intervalCountT_denote`: the term computes
`localIntervalCount`, given terms implementing the interval's data.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.LocalSim

open ProgTerm ProgTerm.Term Cslib.Turing _root_.Turing _root_.Turing.MultiTapePTM
  _root_.Turing.MultiTapeNTM.ChoiceTable

variable {w : List Bool}

def readT (hd L Rt c rho : Term) : Term :=
  ite (eqT c rho) hd
    (ite (lt rho c) (mod (divPowT (const 3) Rt (sub (sub c rho) (const 1))) (const 3))
      (mod (divPowT (const 3) L (sub (sub rho c) (const 1))) (const 3)))

theorem denote_readT (hd L Rt c rho : Term) (env : List ℕ) :
    (readT hd L Rt c rho).denote w env =
      readN (hd.denote w env, L.denote w env, Rt.denote w env) (c.denote w env)
        (rho.denote w env) := by
  unfold readT readN
  simp only [denote_ite, denote_eqT, denote_lt, denote_mod, denote_div, denote_const,
    divPowT_denote _ _ _ _ (stableAt_const _ _), denote_sub]
  by_cases h0 : c.denote w env = rho.denote w env
  · simp [h0]
  · by_cases h1 : rho.denote w env < c.denote w env <;> simp [h0, h1]

theorem ind_mul (p q : Prop) [Decidable p] [Decidable q] :
    (if p then 1 else 0) * (if q then 1 else 0) = if p ∧ q then (1 : ℕ) else 0 := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

theorem ite_iff {P Q : Prop} [Decidable P] [Decidable Q] (h : P ↔ Q) :
    (if P then (1 : ℕ) else 0) = if Q then 1 else 0 := by
  by_cases hp : P
  · rw [if_pos hp, if_pos (h.mp hp)]
  · rw [if_neg hp, if_neg (fun hq => hp (h.mpr hq))]

theorem ind_shape (p1 p2 a c p4 p5 : Prop) [Decidable p1] [Decidable p2] [Decidable a]
    [Decidable c] [Decidable p4] [Decidable p5] :
    (if p1 then 1 else 0) * ((if p2 then 1 else 0) * (((if a then 1 else 0) * (if c then 1 else 0))
      * ((if p4 then 1 else 0) * (if p5 then 1 else 0)))) =
      if p1 ∧ p2 ∧ (a ∧ c) ∧ p4 ∧ p5 then (1 : ℕ) else 0 := by
  by_cases h1 : p1 <;> by_cases h2 : p2 <;> by_cases h3 : a <;> by_cases h4 : c <;>
    by_cases h5 : p4 <;> by_cases h6 : p5 <;> simp [h1, h2, h3, h4, h5, h6]

/-- The test of the interval condition on the packed configuration `a`. -/
def condT (k : ℕ) (bT JpT JmT stO trO : Term) (offO dC cellO : Term → Term) (R a : Term) :
    Term :=
  mul (eqT (digitT R a (const 0)) stO) (mul (eqT (digitT R a (const 2)) trO)
    (mul (mul (lt (offO (const 0)) bT)
      (eqT (add (add (digitT R a (const 1)) (mul bT JmT)) bT)
        (add (add (add (const 1) (mul bT JpT)) (mul bT (dC (const 0)))) (offO (const 0)))))
    (mul (allT (const k) fun h => mul (lt (offO (add h (const 1))) bT)
        (eqT (digitT R a (add (add (const 3) (mul (const 4) h)) (const 3)))
          (add (mul bT (dC (add h (const 1)))) (offO (add h (const 1))))))
      (allT (const k) fun h => allT (mul (const 3) bT) fun c =>
        eqT (cellO (add (mul h (mul (const 3) bT)) c))
          (readT (digitT R a (add (const 3) (mul (const 4) h)))
            (digitT R a (add (add (const 3) (mul (const 4) h)) (const 1)))
            (digitT R a (add (add (const 3) (mul (const 4) h)) (const 2))) c
            (digitT R a (add (add (const 3) (mul (const 4) h)) (const 3))))))))

open Classical in
theorem denote_condT (k : ℕ) {bT JpT JmT stO trO R a : Term} {offO dC cellO : Term → Term}
    {OffO DC CellO : ℕ → ℕ} {env : List ℕ} (hb : StableAt w bT env) (hR : StableAt w R env)
    (ha : StableAt w a env) (hJp : StableAt w JpT env) (hJm : StableAt w JmT env)
    (hoff : ImplementsFun w env offO OffO) (hdc : ImplementsFun w env dC DC)
    (hcell : ImplementsFun w env cellO CellO) :
    (condT k bT JpT JmT stO trO offO dC cellO R a).denote w env =
      if condN k (bT.denote w env) (JpT.denote w env) (JmT.denote w env) (stO.denote w env)
          (trO.denote w env) OffO DC CellO (R.denote w env) (a.denote w env) then 1 else 0 := by
  set b := bT.denote w env
  set Rv := R.denote w env
  set av := a.denote w env
  -- the per-tape test
  have t1 : ∀ acc h, (mul (lt (offO (add (lvl env.length) (const 1))) bT)
      (eqT (digitT R a (add (add (const 3) (mul (const 4) (lvl env.length))) (const 3)))
        (add (mul bT (dC (add (lvl env.length) (const 1)))) (offO (add (lvl env.length)
          (const 1)))))).denote w (acc :: h :: env) =
      if OffO (h + 1) < b ∧ digN Rv av (3 + 4 * h + 3) = b * DC (h + 1) + OffO (h + 1)
      then 1 else 0 := by
    intro acc h
    have hA : StableAt w (add (lvl env.length) (const 1)) ([acc, h] ++ env) :=
      (stableAt_lvl (by simp)).add (stableAt_const _ _)
    have hR' : StableAt w R (acc :: h :: env) := hR.extend [acc, h]
    have o1 := (hoff [acc, h] _ hA).1
    have d1 := (hdc [acc, h] _ hA).1
    simp only [List.cons_append, List.nil_append] at o1 d1
    simp only [denote_mul, denote_lt, denote_eqT, denote_add, denote_const, o1, d1,
      digitT_denote _ _ _ _ hR', hb.cons₂, hR.cons₂, ha.cons₂, denote_lvl_index]
    rw [← ind_mul]; rfl
  -- the per-cell test
  have t2 : ∀ acc h acc' c, (eqT (cellO (add (mul (lvl env.length) (mul (const 3) bT))
        (lvl (env.length + 2))))
      (readT (digitT R a (add (const 3) (mul (const 4) (lvl env.length))))
        (digitT R a (add (add (const 3) (mul (const 4) (lvl env.length))) (const 1)))
        (digitT R a (add (add (const 3) (mul (const 4) (lvl env.length))) (const 2)))
        (lvl (env.length + 2))
        (digitT R a (add (add (const 3) (mul (const 4) (lvl env.length))) (const 3))))).denote w
        (acc' :: c :: acc :: h :: env) =
      if CellO (h * (3 * b) + c) = readN (digN Rv av (3 + 4 * h), digN Rv av (3 + 4 * h + 1),
        digN Rv av (3 + 4 * h + 2)) c (digN Rv av (3 + 4 * h + 3)) then 1 else 0 := by
    intro acc h acc' c
    have l0 : (lvl env.length).denote w (acc' :: c :: acc :: h :: env) = h := by
      rw [denote_lvl]; simp only [List.length_cons]
      rw [show env.length + 1 + 1 + 1 + 1 - env.length - 1 = 3 by omega]; rfl
    have l2 : (lvl (env.length + 2)).denote w (acc' :: c :: acc :: h :: env) = c := by
      rw [denote_lvl]; simp only [List.length_cons]
      rw [show env.length + 1 + 1 + 1 + 1 - (env.length + 2) - 1 = 1 by omega]; rfl
    have hR4' : StableAt w R (acc' :: c :: acc :: h :: env) := hR.extend [acc', c, acc, h]
    have hA : StableAt w (add (mul (lvl env.length) (mul (const 3) bT)) (lvl (env.length + 2)))
        ([acc', c, acc, h] ++ env) :=
      ((stableAt_lvl
          (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)).mul
        ((stableAt_const _ _).mul (hb.extend _))).add
        (stableAt_lvl (by simp only [List.length_append, List.length_cons, List.length_nil]; omega))
    have c1 := (hcell [acc', c, acc, h] _ hA).1
    simp only [List.cons_append, List.nil_append] at c1
    have hb4 : bT.denote w (acc' :: c :: acc :: h :: env) = b := hb [acc', c, acc, h]
    have hR4 : R.denote w (acc' :: c :: acc :: h :: env) = Rv := hR [acc', c, acc, h]
    have ha4 : a.denote w (acc' :: c :: acc :: h :: env) = av := ha [acc', c, acc, h]
    simp only [denote_eqT, c1, denote_readT, digitT_denote _ _ _ _ hR4',
      denote_add, denote_mul, denote_const, l0, l2, hb4, hR4, ha4, digN]
    congr
  have hall2 : ∀ acc h, (allT (mul (const 3) bT) fun c =>
      eqT (cellO (add (mul (lvl env.length) (mul (const 3) bT)) c))
        (readT (digitT R a (add (const 3) (mul (const 4) (lvl env.length))))
          (digitT R a (add (add (const 3) (mul (const 4) (lvl env.length))) (const 1)))
          (digitT R a (add (add (const 3) (mul (const 4) (lvl env.length))) (const 2))) c
          (digitT R a (add (add (const 3) (mul (const 4) (lvl env.length))) (const 3))))).denote w
        (acc :: h :: env) =
      if ∀ c < 3 * b, CellO (h * (3 * b) + c) = readN (digN Rv av (3 + 4 * h),
        digN Rv av (3 + 4 * h + 1), digN Rv av (3 + 4 * h + 2)) c (digN Rv av (3 + 4 * h + 3))
      then 1 else 0 := by
    intro acc h
    rw [allT_denote _ _ (acc :: h :: env) _ fun acc' c => by
      have := t2 acc h acc' c
      simpa using this]
    simp [hb.cons₂, b]
  unfold condT
  simp only [denote_mul]
  rw [allT_denote _ _ env _ fun acc h => t1 acc h,
    allT_denote _ _ env _ fun acc h => hall2 acc h]
  rw [denote_eqT, denote_eqT, denote_lt, denote_eqT, ind_shape]
  apply ite_iff
  unfold condN digN
  simp only [denote_add, denote_mul, denote_const, digitT_denote _ _ _ _ hR,
    hoff.den (stableAt_const _ _), hdc.den (stableAt_const _ _), b, Rv, av]

end Cslib.Complexity.NtimeDspace.LocalSim
