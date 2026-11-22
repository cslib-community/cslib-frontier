/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.ThreeSat.Terms

/-!
# The accessors of the 3-SAT network, as terms

Terms for the numbers of edges and vertices (`edgesT`, `vertsT`), the ends of an edge (`endUT`,
`endWT`), the degree and the ports of a vertex (`degT'`, `portT'`) and the vertex functions
(`funT`) of the network `(rawW w s).net`, with their values (`val_*`): `6m`, `7m`, `Raw.uN`,
`Raw.wN`, the length of `Raw.portsN`, its entries, and the vertex function `Raw.evalN` at the bits
of a number `A` on the ports (`funN`).
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Cross.ThreeSat

open NtimeDspace.ProgLang NtimeDspace.ProgTerm Term NtimeDspace.Cross.Exact Finset

variable {w : List Bool} {M : ℕ} {env : List ℕ}

/-! ### Semantics on numbers -/

namespace Raw

variable (d : Raw)

/-- The bits of `A` on `len` ports. -/
def bitsAt (A len : ℕ) : List Bool := List.ofFn fun j : Fin len => A.testBit j

/-- The vertex function of `v` at the bits of `A`, as a number. -/
def funN (v A : ℕ) : ℕ := (d.evalN v (bitsAt A (d.portsN v).length)).toNat

/-- The `j`-th port of `v`, on numbers. -/
def portNum (v j : ℕ) : ℕ :=
  if v < d.m then 3 * v + j
  else if v < 4 * d.m then
    (if j < 1 then v - d.m else if j < 2 then 3 * d.m + (v - d.m) else 3 * d.m + d.prev (v - d.m))
  else 3 * d.m + (v - 4 * d.m)

/-- The degree of `v`, on numbers. -/
def degNum (v : ℕ) : ℕ :=
  if v < d.m then 3
  else if v < 4 * d.m then 2 + (d.hasPrev (v - d.m)).toNat else 1 - (d.hasNext (v - 4 * d.m)).toNat

/-- The clause indicator at the bits of `A`. -/
def clauseN (c A : ℕ) : ℕ :=
  ((d.pres (3 * c) || !A.testBit 0) && (d.pres (3 * c + 1) || !A.testBit 1) &&
    (d.pres (3 * c + 2) || !A.testBit 2) &&
    ((d.pres (3 * c) && (A.testBit 0 == d.sign (3 * c))) ||
      (d.pres (3 * c + 1) && (A.testBit 1 == d.sign (3 * c + 1))) ||
      (d.pres (3 * c + 2) && (A.testBit 2 == d.sign (3 * c + 2))))).toNat

/-- The occurrence indicator at the bits of `A`. -/
def occN (t A : ℕ) : ℕ :=
  ((!d.hasNext t || A.testBit 0 == A.testBit 1) &&
      (!d.hasPrev t || A.testBit 0 == A.testBit 2)).toNat

/-- The sink indicator at the bits of `A`. -/
def sinkN (t A : ℕ) : ℕ := (d.hasNext t || !A.testBit 0).toNat

variable {d}

theorem length_portsN (v : ℕ) : (d.portsN v).length = d.degNum v := by
  unfold portsN degNum
  split_ifs with h1 h2 h3 h4 <;> simp_all

theorem getElem_portsN {v j : ℕ} (hj : j < (d.portsN v).length) :
    (d.portsN v)[j] = d.portNum v j := by
  by_cases h1 : v < d.m
  · simp only [portsN, portNum, h1, ite_true] at hj ⊢
    have : j < 3 := by simpa using hj
    interval_cases j <;> rfl
  · by_cases h4 : v < 4 * d.m
    · cases hp : d.hasPrev (v - d.m)
      · simp only [portsN, portNum, h1, h4, hp, ite_true, ite_false, Bool.false_eq_true,
          List.append_nil] at hj ⊢
        have : j < 2 := by simpa using hj
        interval_cases j <;> rfl
      · simp only [portsN, portNum, h1, h4, hp, ite_true, ite_false, List.cons_append,
          List.nil_append] at hj ⊢
        have : j < 3 := by simpa using hj
        interval_cases j <;> rfl
    · cases hn : d.hasNext (v - 4 * d.m)
      · simp only [portsN, portNum, h1, h4, hn, ite_false, Bool.false_eq_true] at hj ⊢
        have : j < 1 := by simpa using hj
        interval_cases j; rfl
      · simp [portsN, h1, h4, hn] at hj

theorem getD_bitsAt {A len j : ℕ} (hj : j < len) : (bitsAt A len).getD j false = A.testBit j := by
  simp [bitsAt, hj]

theorem funN_eq (v A : ℕ) :
    d.funN v A = if v < d.m then d.clauseN v A
      else if v < 4 * d.m then d.occN (v - d.m) A else d.sinkN (v - 4 * d.m) A := by
  unfold funN evalN
  by_cases h1 : v < d.m
  · have hl : (d.portsN v).length = 3 := by rw [length_portsN]; simp [degNum, h1]
    have hb : bitsAt A 3 = [A.testBit 0, A.testBit 1, A.testBit 2] := by
      simp [bitsAt, List.ofFn_succ]
    simp only [h1, ite_true, clauseOK, clauseN, hl, hb]
    simp [List.range_succ, Bool.and_assoc, Bool.or_assoc]
  · by_cases h4 : v < 4 * d.m
    · simp only [h1, h4, ite_false, ite_true, occOK, occN]
      have hl : (d.portsN v).length = 2 + (d.hasPrev (v - d.m)).toNat := by
        rw [length_portsN]; simp [degNum, h1, h4]
      rw [hl, getD_bitsAt (by omega), getD_bitsAt (by omega)]
      cases hp : d.hasPrev (v - d.m)
      · simp
      · rw [getD_bitsAt (by simp)]
    · simp only [h1, h4, ite_false, sinkOK, sinkN]
      have hl : (d.portsN v).length = 1 - (d.hasNext (v - 4 * d.m)).toNat := by
        rw [length_portsN]; simp [degNum, h1, h4]
      cases hn : d.hasNext (v - 4 * d.m)
      · rw [hl, hn, getD_bitsAt (by simp)]
      · simp

end Raw

/-! ### The terms -/

/-- The number of edges `6m`. -/
def edgesT (sT : Term) : Term := mul (const 6) (mT sT)
/-- The number of vertices `7m`. -/
def vertsT (sT : Term) : Term := mul (const 7) (mT sT)
/-- `4 m`. -/
def m4T (sT : Term) : Term := mul (const 4) (mT sT)

/-- The row end of edge `i`. -/
def endUT (sT iT : Term) : Term :=
  ite (lt iT (m3T sT)) (div iT (const 3)) (add (mT sT) (sub iT (m3T sT)))

/-- The column end of edge `i`. -/
def endWT (sT iT : Term) : Term :=
  ite (lt iT (m3T sT)) (add (mT sT) iT)
    (ite (hasNextT sT (sub iT (m3T sT))) (add (mT sT) (nextT sT (sub iT (m3T sT))))
      (add (m4T sT) (sub iT (m3T sT))))

/-- The degree of vertex `v`. -/
def degT' (sT vT : Term) : Term :=
  ite (lt vT (mT sT)) (const 3)
    (ite (lt vT (m4T sT)) (add (const 2) (hasPrevT sT (sub vT (mT sT))))
      (sub (const 1) (hasNextT sT (sub vT (m4T sT)))))

/-- The `j`-th port of vertex `v`. -/
def portT' (sT vT jT : Term) : Term :=
  ite (lt vT (mT sT)) (add (mul (const 3) vT) jT)
    (ite (lt vT (m4T sT))
      (ite (lt jT (const 1)) (sub vT (mT sT))
        (ite (lt jT (const 2)) (add (m3T sT) (sub vT (mT sT)))
          (add (m3T sT) (prevT sT (sub vT (mT sT))))))
      (add (m3T sT) (sub vT (m4T sT))))

/-- `p ∨ ¬b`, for `0/1` values. -/
def impT (pT bT : Term) : Term := sub (const 1) (mul (sub (const 1) pT) bT)
/-- `p ∧ (b = σ)`, for `0/1` values. -/
def hitT (pT bT σT : Term) : Term := mul pT (Exact.eqT bT σT)

/-- The clause indicator of clause `c` at the bits of `A`. -/
def clauseT (sT cT AT : Term) : Term :=
  let slot := fun j : ℕ => add (mul (const 3) cT) (const j)
  mul (mul (impT (presT sT (slot 0)) (bit AT (const 0)))
      (mul (impT (presT sT (slot 1)) (bit AT (const 1)))
          (impT (presT sT (slot 2)) (bit AT (const 2)))))
    (lt (const 0) (add (hitT (presT sT (slot 0)) (bit AT (const 0)) (signT sT (slot 0)))
      (add (hitT (presT sT (slot 1)) (bit AT (const 1)) (signT sT (slot 1)))
        (hitT (presT sT (slot 2)) (bit AT (const 2)) (signT sT (slot 2))))))

/-- The occurrence indicator of slot `t` at the bits of `A`. -/
def occT (sT tT AT : Term) : Term :=
  mul (sub (const 1) (mul (hasNextT sT tT)
      (sub (const 1) (Exact.eqT (bit AT (const 0)) (bit AT (const 1))))))
    (sub (const 1) (mul (hasPrevT sT tT)
        (sub (const 1) (Exact.eqT (bit AT (const 0)) (bit AT (const 2))))))

/-- The sink indicator of slot `t` at the bits of `A`. -/
def sinkT (sT tT AT : Term) : Term :=
  sub (const 1) (mul (sub (const 1) (hasNextT sT tT)) (bit AT (const 0)))

/-- The vertex function of `v` at the bits of `A`. -/
def funT (sT vT AT : Term) : Term :=
  ite (lt vT (mT sT)) (clauseT sT vT AT)
    (ite (lt vT (m4T sT)) (occT sT (sub vT (mT sT)) AT) (sinkT sT (sub vT (m4T sT)) AT))

/-! ### Values -/

@[simp] theorem pos_toNat {b : Bool} : 0 < b.toNat ↔ b = true := by cases b <;> simp

section Values

variable {sT iT vT jT AT tT : Term} {s i v j A t : ℕ}

theorem toNat_bit (A j : ℕ) : A / 2 ^ j % 2 = (A.testBit j).toNat := (Nat.toNat_testBit A j).symm

theorem val_bitT {AT : Term} {A : ℕ} (hA : Val w AT env A) (j : ℕ) :
    Val w (bit AT (const j)) env (A.testBit j).toNat := by
  have := val_bit hA (val_const j env)
  rwa [toNat_bit] at this

theorem val_edgesT (hs : Val w sT env s) : Val w (edgesT sT) env (6 * (rawW w s).m) := by
  have h := val_mul (val_const 6 env) (val_mT hs); exact h

theorem val_vertsT (hs : Val w sT env s) : Val w (vertsT sT) env (7 * (rawW w s).m) := by
  have h := val_mul (val_const 7 env) (val_mT hs); exact h

theorem val_m4T (hs : Val w sT env s) : Val w (m4T sT) env (4 * (rawW w s).m) := by
  have h := val_mul (val_const 4 env) (val_mT hs); exact h

theorem val_endUT (hs : Val w sT env s) (hi : Val w iT env i) :
    Val w (endUT sT iT) env ((rawW w s).uN i) := by
  have h := val_ite (val_lt hi (val_m3T hs)) (val_div hi (val_const 3 env))
    (val_add (val_mT hs) (val_sub hi (val_m3T hs)))
  refine fun extra => (h extra).trans ?_
  simp only [Raw.uN]
  by_cases h1 : i < 3 * (rawW w s).m <;> simp [h1]

theorem val_endWT (hs : Val w sT env s) (hi : Val w iT env i) :
    Val w (endWT sT iT) env ((rawW w s).wN i) := by
  have hj := val_sub hi (val_m3T hs)
  have h := val_ite (val_lt hi (val_m3T hs)) (val_add (val_mT hs) hi)
    (val_ite (val_hasNextT hs hj) (val_add (val_mT hs) (val_nextT hs hj))
      (val_add (val_m4T hs) hj))
  refine fun extra => (h extra).trans ?_
  simp only [Raw.wN]
  by_cases h1 : i < 3 * (rawW w s).m
  · simp [h1]
  · cases hn : (rawW w s).hasNext (i - 3 * (rawW w s).m) <;> simp [h1]

theorem val_degT' (hs : Val w sT env s) (hv : Val w vT env v) :
    Val w (degT' sT vT) env ((rawW w s).portsN v).length := by
  have h := val_ite (val_lt hv (val_mT hs)) (val_const 3 env)
    (val_ite (val_lt hv (val_m4T hs)) (val_add (val_const 2 env)
        (val_hasPrevT hs (val_sub hv (val_mT hs))))
      (val_sub (val_const 1 env) (val_hasNextT hs (val_sub hv (val_m4T hs)))))
  refine fun extra => (h extra).trans ?_
  rw [Raw.length_portsN, Raw.degNum]
  by_cases h1 : v < (rawW w s).m
  · simp [h1]
  · by_cases h4 : v < 4 * (rawW w s).m <;> simp [h1, h4]

theorem val_portT' (hs : Val w sT env s) (hv : Val w vT env v) (hj : Val w jT env j) :
    Val w (portT' sT vT jT) env ((rawW w s).portNum v j) := by
  have hvm := val_sub hv (val_mT hs)
  have h := val_ite (val_lt hv (val_mT hs)) (val_add (val_mul (val_const 3 env) hv) hj)
    (val_ite (val_lt hv (val_m4T hs))
      (val_ite (val_lt hj (val_const 1 env)) hvm
        (val_ite (val_lt hj (val_const 2 env)) (val_add (val_m3T hs) hvm)
          (val_add (val_m3T hs) (val_prevT hs hvm))))
      (val_add (val_m3T hs) (val_sub hv (val_m4T hs))))
  refine fun extra => (h extra).trans ?_
  simp only [Raw.portNum]
  by_cases h1 : v < (rawW w s).m
  · simp [h1]
  · by_cases h4 : v < 4 * (rawW w s).m
    · by_cases j1 : j < 1
      · simp [h1, h4, j1]
      · by_cases j2 : j < 2 <;> simp [h1, h4, j1, j2]
    · simp [h1, h4]

theorem val_impT {pT bT : Term} {p b : Bool} (hp : Val w pT env p.toNat)
    (hb : Val w bT env b.toNat) :
    Val w (impT pT bT) env (p || !b).toNat := by
  have h := val_sub (val_const 1 env) (val_mul (val_sub (val_const 1 env) hp) hb)
  refine fun extra => (h extra).trans ?_
  cases p <;> cases b <;> rfl

theorem val_hitT {pT bT σT : Term} {p b σ : Bool} (hp : Val w pT env p.toNat)
    (hb : Val w bT env b.toNat) (hσ : Val w σT env σ.toNat) :
    Val w (hitT pT bT σT) env (p && (b == σ)).toNat := by
  have h := val_mul hp (val_eqT hb hσ)
  refine fun extra => (h extra).trans ?_
  cases p <;> cases b <;> cases σ <;> rfl

theorem toNat_and (a b : Bool) : (a && b).toNat = a.toNat *
    b.toNat := by cases a <;> cases b <;> rfl

theorem toNat_or3 (a b c : Bool) :
    (a || b || c).toNat = if 0 < a.toNat + (b.toNat + c.toNat) then 1 else 0 := by
  cases a <;> cases b <;> cases c <;> rfl

theorem val_clauseT (hs : Val w sT env s) (hc : Val w vT env v) (hA : Val w AT env A) :
    Val w (clauseT sT vT AT) env ((rawW w s).clauseN v A) := by
  have hsl : ∀ j : ℕ, Val w (add (mul (const 3) vT) (const j)) env (3 * v + j) := fun j =>
    val_add (val_mul (val_const 3 env) hc) (val_const j env)
  have h := val_mul (val_mul (val_impT (val_presT hs (hsl 0)) (val_bitT hA 0))
      (val_mul (val_impT (val_presT hs (hsl 1)) (val_bitT hA 1))
        (val_impT (val_presT hs (hsl 2)) (val_bitT hA 2))))
    (val_lt (val_const 0 env) (val_add (val_hitT (val_presT hs (hsl 0)) (val_bitT hA 0)
        (val_signT hs (hsl 0)))
      (val_add (val_hitT (val_presT hs (hsl 1)) (val_bitT hA 1) (val_signT hs (hsl 1)))
        (val_hitT (val_presT hs (hsl 2)) (val_bitT hA 2) (val_signT hs (hsl 2))))))
  refine fun extra => (h extra).trans ?_
  rw [Raw.clauseN]
  simp only [Nat.add_zero]
  generalize (rawW w s).pres (3 * v) = p0
  generalize (rawW w s).pres (3 * v + 1) = p1
  generalize (rawW w s).pres (3 * v + 2) = p2
  generalize (rawW w s).sign (3 * v) = s0
  generalize (rawW w s).sign (3 * v + 1) = s1
  generalize (rawW w s).sign (3 * v + 2) = s2
  generalize A.testBit 0 = b0
  generalize A.testBit 1 = b1
  generalize A.testBit 2 = b2
  revert p0 p1 p2 s0 s1 s2 b0 b1 b2
  decide

theorem val_occT (hs : Val w sT env s) (ht : Val w tT env t) (hA : Val w AT env A) :
    Val w (occT sT tT AT) env ((rawW w s).occN t A) := by
  have h := val_mul (val_sub (val_const 1 env) (val_mul (val_hasNextT hs ht)
      (val_sub (val_const 1 env) (val_eqT (val_bitT hA 0) (val_bitT hA 1)))))
    (val_sub (val_const 1 env) (val_mul (val_hasPrevT hs ht)
      (val_sub (val_const 1 env) (val_eqT (val_bitT hA 0) (val_bitT hA 2)))))
  refine fun extra => (h extra).trans ?_
  rw [Raw.occN]
  cases (rawW w s).hasNext t <;> cases (rawW w s).hasPrev t <;> cases A.testBit 0 <;>
    cases A.testBit 1 <;> cases A.testBit 2 <;> rfl

theorem val_sinkT (hs : Val w sT env s) (ht : Val w tT env t) (hA : Val w AT env A) :
    Val w (sinkT sT tT AT) env ((rawW w s).sinkN t A) := by
  have h := val_sub (val_const 1 env) (val_mul (val_sub (val_const 1 env) (val_hasNextT hs ht))
    (val_bitT hA 0))
  refine fun extra => (h extra).trans ?_
  rw [Raw.sinkN]
  cases (rawW w s).hasNext t <;> cases A.testBit 0 <;> rfl

theorem val_funT (hs : Val w sT env s) (hv : Val w vT env v) (hA : Val w AT env A) :
    Val w (funT sT vT AT) env ((rawW w s).funN v A) := by
  have h := val_ite (val_lt hv (val_mT hs)) (val_clauseT hs hv hA)
    (val_ite (val_lt hv (val_m4T hs)) (val_occT hs (val_sub hv (val_mT hs)) hA)
      (val_sinkT hs (val_sub hv (val_m4T hs)) hA))
  refine fun extra => (h extra).trans ?_
  rw [Raw.funN_eq]
  by_cases h1 : v < (rawW w s).m
  · simp [h1]
  · by_cases h4 : v < 4 * (rawW w s).m <;> simp [h1, h4]

end Values

end Cslib.Complexity.NtimeDspace.Cross.ThreeSat
