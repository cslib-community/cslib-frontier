/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.NetIntervalData
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.NetPortTerm

/-!
# The interval tensor entry as a term

`intervalEntryT` computes `intervalEntryNum` (the tensor entry of interval `i`
of the explicit block network) from a term `L` giving the letter numbers of
the edges. It decodes the interval's data from the letters and runs the
interval count term.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.LocalSim

open ProgTerm ProgTerm.Term Cslib.Turing _root_.Turing _root_.Turing.MultiTapePTM
  _root_.Turing.MultiTapeNTM.ChoiceTable

variable {w : List Bool}

/-- A term function implements `F` when its meaning is `F` of its argument's
meaning on every extension of `base`. -/
theorem implementsFun_of_denote {base : List ℕ} {f : Term → Term} {F : ℕ → ℕ}
    (h : ∀ extra a, StableAt w a (extra ++ base) →
      (f a).denote w (extra ++ base) = F (a.denote w (extra ++ base))) :
    ImplementsFun w base f F := fun extra a ha =>
  ⟨h extra a ha, fun extra' => by
    rw [← List.append_assoc, h (extra' ++ extra) a (by rw [List.append_assoc]; exact ha.extend _),
      h extra a ha, List.append_assoc, ha extra']⟩

/-! ### Decoding terms -/

section Terms

variable (k s : ℕ)

/-- The term computing `cradix k b`, the radix `b ^ (k + 1) * 3` of control records. -/
def cradT (bT : Term) : Term := mul (powT bT (const (k + 1))) (const 3)
/-- The term computing `controlCount k s b`, the number of control records. -/
def ccountT (bT : Term) : Term := mul (const (s + 1)) (cradT k bT)
/-- The term computing `ctlSt k s b n`, the state code of the control record numbered `n`. -/
def ctlStT (bT n : Term) : Term :=
  mod (ite (lt (div n (cradT k bT)) (const s)) (div n (cradT k bT)) (const s)) (const (s + 1))
/-- The term computing `ctlOff k b n c`, the offset of head index `c` in the control record
numbered `n`. -/
def ctlOffT (bT n c : Term) : Term :=
  mod (divPowT bT (div (mod n (cradT k bT)) (const 3)) c) bT
/-- The term computing `ctlTr k b n`, the track code of the control record numbered `n`. -/
def ctlTrT (bT n : Term) : Term := mod (mod n (cradT k bT)) (const 3)
/-- The term computing `contCell k s b n r`, the code of cell `r` of the block contents numbered
`n`. -/
def contCellT (bT n r : Term) : Term :=
  ite (lt n (ccountT k s bT)) (const 0) (mod (divPowT (const 3) (sub n (ccountT k s bT)) r)
    (const 3))

/-- The term computing `portOfNum k σ c i i' δ`, the window entry of block `δ` of interval `i`'s
window in the window of interval `i'`. -/
def portOfT (σT cT iT i'T δT : Term) : Term :=
  mod (sub (add (add (digitCountT k σT cT (const 2) iT) (digitCountT k σT cT (const 0) i'T)) δT)
    (add (digitCountT k σT cT (const 0) iT) (digitCountT k σT cT (const 2) i'T))) (const 3)

end Terms

variable {k s : ℕ}

theorem denote_cradT {bT : Term} {env : List ℕ} (hb : StableAt w bT env) :
    (cradT k bT).denote w env = cradix k (bT.denote w env) := by
  simp [cradT, cradix, powT_denote _ _ _ hb]

theorem denote_ccountT {bT : Term} {env : List ℕ} (hb : StableAt w bT env) :
    (ccountT k s bT).denote w env = controlCount k s (bT.denote w env) := by
  simp [ccountT, denote_cradT hb, controlCount, cradix]

theorem denote_ctlStT {bT : Term} (n : Term) {env : List ℕ} (hb : StableAt w bT env) :
    (ctlStT k s bT n).denote w env = ctlSt k s (bT.denote w env) (n.denote w env) := by
  simp only [ctlStT, ctlSt, denote_mod, denote_ite, denote_lt, denote_div, denote_const,
    denote_cradT hb, min_def]
  split_ifs <;> first | rfl | omega

theorem denote_ctlOffT {bT : Term} (n c : Term) {env : List ℕ} (hb : StableAt w bT env) :
    (ctlOffT k bT n c).denote w env = ctlOff k (bT.denote w env) (n.denote w env)
        (c.denote w env) := by
  simp [ctlOffT, ctlOff, denote_cradT hb, divPowT_denote _ _ _ _ hb]

theorem denote_ctlTrT {bT : Term} (n : Term) {env : List ℕ} (hb : StableAt w bT env) :
    (ctlTrT k bT n).denote w env = ctlTr k (bT.denote w env) (n.denote w env) := by
  simp [ctlTrT, ctlTr, denote_cradT hb]

theorem denote_contCellT {bT : Term} (n r : Term) {env : List ℕ} (hb : StableAt w bT env) :
    (contCellT k s bT n r).denote w env =
      contCell k s (bT.denote w env) (n.denote w env) (r.denote w env) := by
  simp only [contCellT, contCell, denote_ite, denote_lt, denote_ccountT hb, denote_const,
    denote_mod, denote_sub, divPowT_denote _ _ _ _ (stableAt_const _ _)]
  split_ifs <;> first | rfl | omega

theorem denote_portOfT {σT cT : Term} (iT i'T δT : Term) {env : List ℕ}
    (hσ : StableAt w σT env) (hc : StableAt w cT env) :
    (portOfT k σT cT iT i'T δT).denote w env =
      portOfNum k (σT.denote w env) (cT.denote w env) (iT.denote w env) (i'T.denote w env)
        (δT.denote w env) := by
  simp [portOfT, portOfNum, denote_digitCountT k _ hσ hc (stableAt_const _ _)]

theorem StableAt.portOfT {σT cT iT i'T δT : Term} {env : List ℕ}
    (hσ : StableAt w σT env) (hc : StableAt w cT env) (hi : StableAt w iT env)
    (hi' : StableAt w i'T env) (hd : StableAt w δT env) :
    StableAt w (portOfT k σT cT iT i'T δT) env := fun extra => by
  rw [denote_portOfT _ _ _ (hσ.extend extra) (hc.extend extra), denote_portOfT _ _ _ hσ hc,
    hσ extra, hc extra, hi extra, hi' extra, hd extra]

theorem StableAt.contCellT {bT n r : Term} {env : List ℕ} (hb : StableAt w bT env)
    (hn : StableAt w n env) (hr : StableAt w r env) :
    StableAt w (contCellT k s bT n r) env := fun extra => by
  rw [denote_contCellT _ _ (hb.extend extra), denote_contCellT _ _ hb, hb extra, hn extra,
    hr extra]

/-! ### The data of an interval -/

section Data

variable (k s : ℕ)

/-- The term computing `inSt k s b init L i`, the state code entering interval `i`, from the
letter numbers given by `L`. -/
def inStT (init : ℕ) (bT : Term) (L : Term → Term) (iT : Term) : Term :=
  ite (eqT iT (const 0)) (const init)
    (ite (lt (L (sub iT (const 1))) (ccountT k s bT)) (ctlStT k s bT (L (sub iT (const 1))))
      (const 0))

/-- The term computing `inOff k s b L i c`, the offset of head index `c` entering interval `i`. -/
def inOffT (bT : Term) (L : Term → Term) (iT c : Term) : Term :=
  ite (eqT iT (const 0)) (const 0)
    (ite (lt (L (sub iT (const 1))) (ccountT k s bT)) (ctlOffT k bT (L (sub iT (const 1))) c)
      (const 0))

/-- The term computing `inTr k s b L i`, the track code entering interval `i`. -/
def inTrT (bT : Term) (L : Term → Term) (iT : Term) : Term :=
  ite (eqT iT (const 0)) (const 0)
    (ite (lt (L (sub iT (const 1))) (ccountT k s bT)) (ctlTrT k bT (L (sub iT (const 1))))
      (const 0))

/-- Cell `x mod 3b` of the window of tape `x / 3b` entering interval `i`. -/
def inCellT (qT bT σT : Term) (L : Term → Term) (iT x : Term) : Term :=
  ite (eqT (lastBeforeT k σT (add (div x (mul (const 3) bT)) (const 1)) iT
      (div (mod x (mul (const 3) bT)) bT)) (const 0)) (const 0)
    (contCellT k s bT (L (add qT (add (add (portOfT k σT (add (div x (mul (const 3) bT)) (const 1))
        iT (sub (lastBeforeT k σT (add (div x (mul (const 3) bT)) (const 1)) iT
          (div (mod x (mul (const 3) bT)) bT)) (const 1)) (div (mod x (mul (const 3) bT)) bT))
        (mul (const 3) (div x (mul (const 3) bT))))
      (mul (const (k * 3)) (sub (lastBeforeT k σT (add (div x (mul (const 3) bT)) (const 1)) iT
          (div (mod x (mul (const 3) bT)) bT)) (const 1))))))
      (mod (mod x (mul (const 3) bT)) bT))

/-- Cell `x mod 3b` of the window of tape `x / 3b` leaving interval `i`. -/
def outCellT (qT bT : Term) (L : Term → Term) (iT x : Term) : Term :=
  contCellT k s bT (L (add qT (add (add (div (mod x (mul (const 3) bT)) bT)
      (mul (const 3) (div x (mul (const 3) bT)))) (mul (const (k * 3)) iT))))
    (mod (mod x (mul (const 3) bT)) bT)

end Data

section DataLemmas

variable {bT qT σT iT : Term} {L : Term → Term} {Lv : ℕ → ℕ} {env : List ℕ}

theorem denote_inStT (init : ℕ) (hb : StableAt w bT env) (hi : StableAt w iT env)
    (hL : ImplementsFun w env L Lv) :
    (inStT k s init bT L iT).denote w env = inSt k s (bT.denote w env) init Lv
        (iT.denote w env) := by
  have ha : StableAt w (sub iT (const 1)) env := hi.sub (stableAt_const _ _)
  simp only [inStT, inSt, denote_ite, denote_eqT, denote_const, denote_lt, denote_ccountT hb,
    denote_ctlStT _ hb, hL.den ha, denote_sub]
  by_cases h0 : iT.denote w env = 0
  · simp [h0]
  · by_cases h1 : Lv (iT.denote w env - 1) < controlCount k s (bT.denote w env) <;> simp [h0, h1]

theorem denote_inOffT (hb : StableAt w bT env) (hi : StableAt w iT env)
    (hL : ImplementsFun w env L Lv) (c : Term) :
    (inOffT k s bT L iT c).denote w env =
      inOff k s (bT.denote w env) Lv (iT.denote w env) (c.denote w env) := by
  have ha : StableAt w (sub iT (const 1)) env := hi.sub (stableAt_const _ _)
  simp only [inOffT, inOff, denote_ite, denote_eqT, denote_const, denote_lt, denote_ccountT hb,
    denote_ctlOffT _ _ hb, hL.den ha, denote_sub]
  by_cases h0 : iT.denote w env = 0
  · simp [h0]
  · by_cases h1 : Lv (iT.denote w env - 1) < controlCount k s (bT.denote w env) <;> simp [h0, h1]

theorem denote_inTrT (hb : StableAt w bT env) (hi : StableAt w iT env)
    (hL : ImplementsFun w env L Lv) :
    (inTrT k s bT L iT).denote w env = inTr k s (bT.denote w env) Lv (iT.denote w env) := by
  have ha : StableAt w (sub iT (const 1)) env := hi.sub (stableAt_const _ _)
  simp only [inTrT, inTr, denote_ite, denote_eqT, denote_const, denote_lt, denote_ccountT hb,
    denote_ctlTrT _ hb, hL.den ha, denote_sub]
  by_cases h0 : iT.denote w env = 0
  · simp [h0]
  · by_cases h1 : Lv (iT.denote w env - 1) < controlCount k s (bT.denote w env) <;> simp [h0, h1]

theorem denote_inCellT (hq : StableAt w qT env) (hb : StableAt w bT env)
    (hσ : StableAt w σT env) (hi : StableAt w iT env) (hL : ImplementsFun w env L Lv)
    {x : Term} (hx : StableAt w x env) :
    (inCellT k s qT bT σT L iT x).denote w env =
      inCell k (qT.denote w env) s (bT.denote w env) (σT.denote w env) Lv (iT.denote w env)
        (x.denote w env / (3 * bT.denote w env)) (x.denote w env % (3 * bT.denote w env)) := by
  have h3b : StableAt w (mul (const 3) bT) env := (stableAt_const _ _).mul hb
  have hh : StableAt w (add (div x (mul (const 3) bT)) (const 1)) env :=
    (hx.div h3b).add (stableAt_const _ _)
  have hc : StableAt w (div (mod x (mul (const 3) bT)) bT) env := (hx.mod h3b).div hb
  have hlb := StableAt.lastBeforeT k hσ hh hi hc
  have harg : StableAt w (add qT (add (add (portOfT k σT (add (div x (mul (const 3) bT)) (const 1))
        iT (sub (lastBeforeT k σT (add (div x (mul (const 3) bT)) (const 1)) iT
          (div (mod x (mul (const 3) bT)) bT)) (const 1)) (div (mod x (mul (const 3) bT)) bT))
        (mul (const 3) (div x (mul (const 3) bT))))
      (mul (const (k * 3)) (sub (lastBeforeT k σT (add (div x (mul (const 3) bT)) (const 1)) iT
          (div (mod x (mul (const 3) bT)) bT)) (const 1))))) env :=
    hq.add (((StableAt.portOfT hσ hh hi (hlb.sub (stableAt_const _ _)) hc).add
      ((stableAt_const _ _).mul (hx.div h3b))).add
      ((stableAt_const _ _).mul (hlb.sub (stableAt_const _ _))))
  unfold inCellT inCell
  simp only [denote_ite, denote_eqT, denote_const, denote_contCellT _ _ hb, hL.den harg,
    denote_lastBeforeT k hσ hh hi hc]
  simp only [denote_add, denote_div, denote_mul, denote_const, denote_mod, denote_sub,
    denote_portOfT _ _ _ hσ hh, denote_lastBeforeT k hσ hh hi hc]
  by_cases h0 : optCode (lastBeforeNum k (σT.denote w env)
      (x.denote w env / (3 * bT.denote w env) + 1) (iT.denote w env)
      (x.denote w env % (3 * bT.denote w env) / bT.denote w env)) = 0 <;> simp [h0]

theorem denote_outCellT (hq : StableAt w qT env) (hb : StableAt w bT env)
    (hi : StableAt w iT env) (hL : ImplementsFun w env L Lv) {x : Term} (hx : StableAt w x env) :
    (outCellT k s qT bT L iT x).denote w env =
      outCell k (qT.denote w env) s (bT.denote w env) Lv (iT.denote w env)
        (x.denote w env / (3 * bT.denote w env)) (x.denote w env % (3 * bT.denote w env)) := by
  have h3b : StableAt w (mul (const 3) bT) env := (stableAt_const _ _).mul hb
  have harg : StableAt w (add qT (add (add (div (mod x (mul (const 3) bT)) bT)
      (mul (const 3) (div x (mul (const 3) bT)))) (mul (const (k * 3)) iT))) env :=
    hq.add ((((hx.mod h3b).div hb).add ((stableAt_const _ _).mul (hx.div h3b))).add
      ((stableAt_const _ _).mul hi))
  unfold outCellT outCell
  simp only [denote_contCellT _ _ hb, hL.den harg]
  simp [Nat.add_assoc]

end DataLemmas

end Cslib.Complexity.NtimeDspace.LocalSim
