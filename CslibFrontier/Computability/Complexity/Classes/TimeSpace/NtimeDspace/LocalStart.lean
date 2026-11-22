/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.LocalTerm

/-!
# The one-interval simulation as a term: the start

The packed start of an interval, from its data given as terms: the state and
track codes, the input block index `J = Jp - Jm`, the offsets `offI` (index `0`
for the input head, `h + 1` for work tape `h`) and the window cells `cellI`
(cell `c` of tape `h` at index `h * 3b + c`). `startT_denote` shows the term is
`cpack R (nStart …)`.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.LocalSim

open ProgTerm ProgTerm.Term Cslib.Turing _root_.Turing _root_.Turing.MultiTapePTM
  _root_.Turing.MultiTapeNTM.ChoiceTable

variable {w : List Bool}

theorem _root_.Cslib.Complexity.NtimeDspace.ProgTerm.ImplementsFun.extend' {base : List ℕ}
    {f : Term → Term} {F : ℕ → ℕ}
    (h : ImplementsFun w base f F) (pre : List ℕ) : ImplementsFun w (pre ++ base) f F :=
  fun extra a ha => by
    have := h (extra ++ pre) a (by rwa [List.append_assoc])
    rwa [List.append_assoc] at this

theorem _root_.Cslib.Complexity.NtimeDspace.ProgTerm.ImplementsFun.den {base : List ℕ}
    {f : Term → Term} {F : ℕ → ℕ}
    (h : ImplementsFun w base f F) {a : Term} (ha : StableAt w a base) :
    (f a).denote w base = F (a.denote w base) := (h [] a ha).1

theorem _root_.Cslib.Complexity.NtimeDspace.ProgTerm.ImplementsFun.stable {base : List ℕ}
    {f : Term → Term} {F : ℕ → ℕ}
    (h : ImplementsFun w base f F) {a : Term} (ha : StableAt w a base) :
    StableAt w (f a) base := (h [] a ha).2

/-! ### Numeric start -/

/-- The input position at the start: coordinate `b (Jp - Jm) + o`, stored plus one. -/
def ipStart (b N Jp Jm o : ℕ) : ℕ :=
  if b * Jm ≤ b * Jp + o + 1 ∧ b * Jp + o + 1 - b * Jm < N + 2 then b * Jp + o + 1 - b * Jm
  else 0

/-- The left number of a tape with cells `F (base + c)` and head at `pos`. -/
def leftN (F : ℕ → ℕ) (base pos : ℕ) : ℕ :=
  ∑ i ∈ Finset.range pos, F (base + (pos - 1 - i)) * 3 ^ i

/-- The right number of a tape with `L` cells `F (base + c)` and head at `pos`. -/
def rightN (F : ℕ → ℕ) (base pos L : ℕ) : ℕ :=
  ∑ i ∈ Finset.range L, (if pos + 1 + i < L then F (base + (pos + 1 + i)) else 0) * 3 ^ i

/-- Digit `i` of the packed start. -/
def startComp (b N Jp Jm stI trI : ℕ) (OffI CellI : ℕ → ℕ) (i : ℕ) : ℕ :=
  if i = 0 then stI else if i = 1 then ipStart b N Jp Jm (OffI 0) else if i = 2 then trI else
  if (i - 3) % 4 = 0 then CellI ((i - 3) / 4 * (3 * b) + (b + OffI ((i - 3) / 4 + 1)))
  else if (i - 3) % 4 = 1 then leftN CellI ((i - 3) / 4 * (3 * b)) (b + OffI ((i - 3) / 4 + 1))
  else if (i - 3) % 4 = 2 then
    rightN CellI ((i - 3) / 4 * (3 * b)) (b + OffI ((i - 3) / 4 + 1)) (3 * b)
  else b + OffI ((i - 3) / 4 + 1)

variable {k s : ℕ} {State : Type} {e : State ≃ Fin s}

theorem ipStart_eq (b : ℕ) (input : List Bool) (Jp Jm o : ℕ) :
    (inputPosOfCoord input (b * ((Jp : ℤ) - Jm) + o)).val = ipStart b input.length Jp Jm o := by
  unfold inputPosOfCoord ipStart
  have e1 : (b : ℤ) * ((Jp : ℤ) - Jm) + o + 1 = ((b * Jp + o + 1 : ℕ) : ℤ) -
      ((b * Jm : ℕ) : ℤ) := by
    push_cast; ring
  rw [show (b : ℤ) * ((Jp : ℤ) - Jm) + o = (b : ℤ) * ((Jp : ℤ) - Jm) + o from rfl]
  split_ifs with h1 h2 h2
  · simp only; rw [e1]; omega
  · exfalso; apply h2; rw [e1] at h1; omega
  · exfalso; apply h1; rw [e1]; omega
  · rfl

/-- **The numeric start, digit by digit.** -/
theorem startComp_eq (b : ℕ) (input : List Bool) (J : Option (Fin k) → ℤ)
    (cIn : ControlData k State) (wIn : Fin k → List (Option Bool)) (Jp Jm : ℕ)
    (OffI CellI : ℕ → ℕ)
    (hJ : J none = (Jp : ℤ) - Jm) (hoff0 : OffI 0 = cIn.2.1 none)
    (hoff : ∀ h : Fin k, OffI (h + 1) = cIn.2.1 (some h)) (hoffb : ∀ h, cIn.2.1 (some h) < b)
    (hlen : ∀ h, (wIn h).length = 3 * b)
    (hcell : ∀ (h : Fin k) c, c < 3 * b → CellI (h * (3 * b) + c) = cc ((wIn h).getD c none))
    {i : ℕ} (hi : i < width k) :
    startComp b input.length Jp Jm (stc e cIn.1) (trc cIn.2.2) OffI CellI i =
      comp (nStart e b input J cIn wIn) i := by
  unfold startComp
  by_cases h0 : i = 0
  · subst h0; simp [comp, nStart]
  by_cases h1 : i = 1
  · subst h1; simp only [comp, nStart, ite_true, one_ne_zero, ite_false]
    rw [hJ, hoff0, ipStart_eq]
  by_cases h2 : i = 2
  · subst h2; simp [comp, nStart]
  have hh : (i - 3) / 4 < k := by unfold width at hi; omega
  set h : Fin k := ⟨(i - 3) / 4, hh⟩
  have hi' : i = 3 + 4 * (h : ℕ) + (i - 3) % 4 := by simp only [h]; omega
  rw [hi', comp_tape _ h _ (Nat.mod_lt _ (by norm_num)), ← hi']
  simp only [h0, h1, h2, ite_false]
  have hhv : (i - 3) / 4 = (h : ℕ) := rfl
  rw [hhv, hoff h]
  have hpos : b + cIn.2.1 (some h) < 3 * b := by have := hoffb h; omega
  by_cases f0 : (i - 3) % 4 = 0
  · simp only [ite_eq_left f0]
    rw [hcell h _ hpos]; rfl
  by_cases f1 : (i - 3) % 4 = 1
  · simp only [ite_eq_right f0, ite_eq_left f1]
    simp only [nStart, NTape.ofCells]
    unfold leftN packDigits
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [hcell h _ (by have := Finset.mem_range.mp hj; omega)]
  by_cases f2 : (i - 3) % 4 = 2
  · simp only [ite_eq_right f0, ite_eq_right f1, ite_eq_left f2]
    simp only [nStart, NTape.ofCells]
    unfold rightN packDigits
    rw [hlen h]
    refine Finset.sum_congr rfl fun j hj => ?_
    split_ifs with hc
    · rw [hcell h _ hc]
    · beta_reduce
      rw [List.getD_eq_default _ _ (by rw [hlen h]; omega)]; rfl
  · simp only [ite_eq_right f0, ite_eq_right f1, ite_eq_right f2]; rfl

/-! ### The start term -/

/-- The term computing `ipStart b N Jp Jm o`, the input position at the start. -/
def ipStartT (bT NT JpT JmT o : Term) : Term :=
  ite (mul (sub (const 1) (lt (add (add (mul bT JpT) o) (const 1)) (mul bT JmT)))
      (lt (sub (add (add (mul bT JpT) o) (const 1)) (mul bT JmT)) (add NT (const 2))))
    (sub (add (add (mul bT JpT) o) (const 1)) (mul bT JmT)) (const 0)

/-- The term computing `leftN CellI base pos`, the left number of a tape window. -/
def leftT (cellI : Term → Term) (baseT posT : Term) : Term :=
  sumT posT fun j => mul (cellI (add baseT (sub (sub posT (const 1)) j))) (powT (const 3) j)

/-- The term computing `rightN CellI base pos L`, the right number of a tape window. -/
def rightT (cellI : Term → Term) (baseT posT LT : Term) : Term :=
  sumT LT fun j => mul (ite (lt (add (add posT (const 1)) j) LT)
    (cellI (add baseT (add (add posT (const 1)) j))) (const 0)) (powT (const 3) j)

/-- The term computing `startComp b N Jp Jm stI trI OffI CellI i`, digit `i` of the packed start. -/
def startCompT (bT NT JpT JmT stI trI : Term) (offI cellI : Term → Term) (i : Term) : Term :=
  ite (eqT i (const 0)) stI
  (ite (eqT i (const 1)) (ipStartT bT NT JpT JmT (offI (const 0)))
  (ite (eqT i (const 2)) trI
  (ite (eqT (mod (sub i (const 3)) (const 4)) (const 0))
    (cellI (add (mul (div (sub i (const 3)) (const 4)) (mul (const 3) bT))
      (add bT (offI (add (div (sub i (const 3)) (const 4)) (const 1))))))
  (ite (eqT (mod (sub i (const 3)) (const 4)) (const 1))
    (leftT cellI (mul (div (sub i (const 3)) (const 4)) (mul (const 3) bT))
      (add bT (offI (add (div (sub i (const 3)) (const 4)) (const 1)))))
  (ite (eqT (mod (sub i (const 3)) (const 4)) (const 2))
    (rightT cellI (mul (div (sub i (const 3)) (const 4)) (mul (const 3) bT))
      (add bT (offI (add (div (sub i (const 3)) (const 4)) (const 1)))) (mul (const 3) bT))
    (add bT (offI (add (div (sub i (const 3)) (const 4)) (const 1)))))))))

/-- The packed start. -/
def startT (k : ℕ) (R bT NT JpT JmT stI trI : Term) (offI cellI : Term → Term) : Term :=
  sumT (const (width k)) fun i => mul (startCompT bT NT JpT JmT stI trI offI cellI i) (powT R i)

theorem denote_leftT {env : List ℕ} {cellI : Term → Term} {CellI : ℕ → ℕ}
    (hc : ImplementsFun w env cellI CellI) {baseT posT : Term} (hb : StableAt w baseT env)
    (hp : StableAt w posT env) :
    (leftT cellI baseT posT).denote w env =
      leftN CellI (baseT.denote w env) (posT.denote w env) := by
  unfold leftT leftN
  rw [denote_sumT _ _ env (fun j => CellI (baseT.denote w env + (posT.denote w env - 1 - j)) *
    3 ^ j)]
  intro acc j
  have harg : StableAt w (add baseT (sub (sub posT (const 1)) (lvl env.length)))
      ([acc, j] ++ env) :=
    ((hb.extend _).add (((hp.extend _).sub (stableAt_const _ _)).sub (stableAt_lvl (by simp))))
  have hcv := (hc [acc, j] _ harg).1
  simp only [List.cons_append, List.nil_append] at hcv
  rw [denote_mul, hcv, powT_denote _ _ _ (stableAt_const _ _)]
  simp [hb.cons₂, hp.cons₂]

theorem StableAt.leftT {env : List ℕ} {cellI : Term → Term} {CellI : ℕ → ℕ}
    (hc : ImplementsFun w env cellI CellI) {baseT posT : Term} (hb : StableAt w baseT env)
    (hp : StableAt w posT env) : StableAt w (leftT cellI baseT posT) env := fun extra => by
  rw [denote_leftT (hc.extend' extra) (hb.extend extra) (hp.extend extra),
    denote_leftT hc hb hp, hb extra, hp extra]

theorem denote_rightT {env : List ℕ} {cellI : Term → Term} {CellI : ℕ → ℕ}
    (hc : ImplementsFun w env cellI CellI) {baseT posT LT : Term} (hb : StableAt w baseT env)
    (hp : StableAt w posT env) (hL : StableAt w LT env) :
    (rightT cellI baseT posT LT).denote w env =
      rightN CellI (baseT.denote w env) (posT.denote w env) (LT.denote w env) := by
  unfold rightT rightN
  rw [denote_sumT _ _ env (fun j => (if posT.denote w env + 1 + j < LT.denote w env then
    CellI (baseT.denote w env + (posT.denote w env + 1 + j)) else 0) * 3 ^ j)]
  intro acc j
  have harg : StableAt w (add baseT (add (add posT (const 1)) (lvl env.length)))
      ([acc, j] ++ env) :=
    ((hb.extend _).add (((hp.extend _).add (stableAt_const _ _)).add (stableAt_lvl (by simp))))
  rw [denote_mul, powT_denote _ _ _ (stableAt_const _ _), denote_ite, denote_lt]
  simp only [denote_add, denote_const, denote_lvl_index, hp.cons₂, hL.cons₂]
  congr 1
  split_ifs with h1 h2 h2
  · have hcv := (hc [acc, j] _ harg).1
    simp only [List.cons_append, List.nil_append] at hcv
    rw [hcv]
    simp [hb.cons₂, hp.cons₂]
  · omega
  · omega
  · rfl

theorem StableAt.rightT {env : List ℕ} {cellI : Term → Term} {CellI : ℕ → ℕ}
    (hc : ImplementsFun w env cellI CellI) {baseT posT LT : Term} (hb : StableAt w baseT env)
    (hp : StableAt w posT env) (hL : StableAt w LT env) :
    StableAt w (rightT cellI baseT posT LT) env := fun extra => by
  rw [denote_rightT (hc.extend' extra) (hb.extend extra) (hp.extend extra) (hL.extend extra),
    denote_rightT hc hb hp hL, hb extra, hp extra, hL extra]

end Cslib.Complexity.NtimeDspace.LocalSim
