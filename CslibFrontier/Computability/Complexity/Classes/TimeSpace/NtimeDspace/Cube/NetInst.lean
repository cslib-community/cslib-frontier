/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.ExactTerm
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.NetFamily
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.NetTerms
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.SumProduct.Eval

/-!
# Network access for a logspace family (Definition 2.1)

The terms of `NetTerms.lean` read a network `G : EdgeNet ℤ (Fin V)` through the interface `NetT`,
with the value contract `NetAcc` and the tier contract `NetTiers`. This module gives the instance
for a family with logspace access (`LogspaceNetFamily`,
`CslibFrontier/Computability/Complexity/Classes/TimeSpace/NtimeDspace/Cross/NetFamily.lean`): every
accessor
runs the corresponding closed program of the family (`callT1`, `callT2`, `callT3`) on its
arguments and a term `sT` for the size `s`. The tiers come from the space bound of
Definition 2.1 (b): on arguments in range every value arising in a program is at most
`(s + 2)^C`, which is at most `2^(128 L)`, and the results are below `(s + 2)^(C+1) < 2^L`, once
`L ≥ (2C + 3)(⌊log₂ s⌋ + 1)`.

The block networks `G_{x,t,σ}` of Lemma 2.2 have their own instance in `NetInstBlock.lean`.

## Main definitions

* `famNetT F sT`: the network terms of the family `F` at the size term `sT`.

## Main results

* `val_callT1`, `val_callT2`, `val_callT3`, `tm_callT1`, `tm_callT2`, `tm_callT3`: running a closed
  program on argument terms with known values, and its tier from a value bound of the program.
* `famNet_acc`: `NetAcc (F.net w s) w env (famNetT F sT)` for a member `F.Mem w s`, when `sT` has
  value `s`.
* `famNet_evalNonneg`: the vertex functions of a member are nonnegative.
* `famNet_tiers`: `NetTiers (F.net w s) w L env (famNetT F sT)` when `sT` has value `s` and tier
`1`,
  `16 ≤ L` and `(2 C + 3)(⌊log₂ s⌋ + 1) ≤ L` (`C = F.C`).
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Cube.Num

open NtimeDspace.ProgLang NtimeDspace.ProgTerm NtimeDspace.ProgTerm.Term NtimeDspace.Cross
  NtimeDspace.SumProduct

variable {w : List Bool} {L : ℕ} {E env : List ℕ}

/-! ### Numbers of the network at in-range arguments -/

section Net

variable {V : ℕ} {G : EdgeNet ℤ (Fin V)}

theorem uN_of_lt {i : ℕ} (hi : i < G.M) : uN G i = G.u ⟨i, hi⟩ := uN_fin (G := G) ⟨i, hi⟩

theorem wN_of_lt {i : ℕ} (hi : i < G.M) : wN G i = G.w ⟨i, hi⟩ := wN_fin (G := G) ⟨i, hi⟩

theorem degN_of_lt {v : ℕ} (hv : v < V) : degN G v = (G.ports ⟨v, hv⟩).length :=
  degN_fin (G := G) ⟨v, hv⟩

theorem portN_of_lt {v j : ℕ} (hv : v < V) (hj : j < (G.ports ⟨v, hv⟩).length) :
    portN G v j = ((G.ports ⟨v, hv⟩).get ⟨j, hj⟩ : ℕ) := by
  rw [List.get_eq_getElem]; exact portN_fin (G := G) ⟨v, hv⟩ hj

theorem evalN_of_lt {v : ℕ} (hv : v < V) (A : ℕ) :
    evalN G v A =
      (G.eval ⟨v, hv⟩ (List.ofFn fun j : Fin (G.ports ⟨v, hv⟩).length => A.testBit j)).toNat := by
  rw [evalN, dite_eq_left_of_eq_true (eq_true hv)]

end Net

/-! ### Running closed programs on terms

The values `Num.Val` and tiers of a closed program applied to argument terms. -/

section Call

variable {q : Prog} {a b c : Term} {A Bv Cv : ℕ}

theorem Val.cons1 {t : Term} {n : ℕ} (h : Val w E t n) (x : ℕ) : Val w (x :: E) t n := h.ext [x]

theorem denote_callT1v (hq : Prog'.closed 1 q = true) (ha : Val w E a A) :
    (callT1 q a).denote w E = q.eval w [A] := by
  have e1 : (a E.length).eval w E = A := ha.2
  show Prog.eval w (.letIn _ q) E = _
  simp only [Prog.eval, e1]
  exact Prog'.eval_append q [A] E hq

theorem denote_callT2v (hq : Prog'.closed 2 q = true) (ha : Val w E a A) (hb : Val w E b Bv) :
    (callT2 q a b).denote w E = q.eval w [A, Bv] := by
  have e1 : (b E.length).eval w E = Bv := hb.2
  have e2 : (a (E.length + 1)).eval w (Bv :: E) = A := (ha.cons1 Bv).2
  show Prog.eval w (.letIn _ (.letIn _ q)) E = _
  simp only [Prog.eval, e1, e2]
  exact Prog'.eval_append q [A, Bv] E hq

theorem denote_callT3v (hq : Prog'.closed 3 q = true) (ha : Val w E a A) (hb : Val w E b Bv)
    (hc : Val w E c Cv) : (callT3 q a b c).denote w E = q.eval w [A, Bv, Cv] := by
  have e1 : (c E.length).eval w E = Cv := hc.2
  have e2 : (b (E.length + 1)).eval w (Cv :: E) = Bv := (hb.cons1 Cv).2
  have e3 : (a (E.length + 2)).eval w (Bv :: Cv :: E) = A := ((ha.cons1 Cv).cons1 Bv).2
  show Prog.eval w (.letIn _ (.letIn _ (.letIn _ q))) E = _
  simp only [Prog.eval, e1, e2, e3]
  exact Prog'.eval_append q [A, Bv, Cv] E hq

theorem val_callT1 (hq : Prog'.closed 1 q = true) (ha : Val w E a A) :
    Val w E (callT1 q a) (q.eval w [A]) :=
  Val.of_denote _ fun pre => denote_callT1v hq (ha.ext pre)

theorem val_callT2 (hq : Prog'.closed 2 q = true) (ha : Val w E a A) (hb : Val w E b Bv) :
    Val w E (callT2 q a b) (q.eval w [A, Bv]) :=
  Val.of_denote _ fun pre => denote_callT2v hq (ha.ext pre) (hb.ext pre)

theorem val_callT3 (hq : Prog'.closed 3 q = true) (ha : Val w E a A) (hb : Val w E b Bv)
    (hc : Val w E c Cv) : Val w E (callT3 q a b c) (q.eval w [A, Bv, Cv]) :=
  Val.of_denote _ fun pre => denote_callT3v hq (ha.ext pre) (hb.ext pre) (hc.ext pre)

theorem bnd_callT2v {B : ℕ} (hq : Prog'.closed 2 q = true) (hb : b.Bnd w B E) (hbv : Val w E b Bv)
    (ha : a.Bnd w B (Bv :: E)) (hav : Val w E a A) (hqb : q.Bounded w B [A, Bv]) :
    (callT2 q a b).Bnd w B E := by
  have e1 : (b E.length).eval w E = Bv := hbv.2
  have e2 : (a (E.length + 1)).eval w (Bv :: E) = A := (hav.cons1 Bv).2
  show Prog.Bounded w B (.letIn _ (.letIn _ q)) E
  simp only [Prog.Bounded, e1, e2]
  exact ⟨hb, ha, (Prog'.bounded_append B q [A, Bv] E hq).mpr hqb⟩

theorem bnd_callT3v {B : ℕ} (hq : Prog'.closed 3 q = true) (hc : c.Bnd w B E) (hcv : Val w E c Cv)
    (hb : b.Bnd w B (Cv :: E)) (hbv : Val w E b Bv) (ha : a.Bnd w B (Bv :: Cv :: E))
    (hav : Val w E a A) (hqb : q.Bounded w B [A, Bv, Cv]) : (callT3 q a b c).Bnd w B E := by
  have e1 : (c E.length).eval w E = Cv := hcv.2
  have e2 : (b (E.length + 1)).eval w (Cv :: E) = Bv := (hbv.cons1 Cv).2
  have e3 : (a (E.length + 2)).eval w (Bv :: Cv :: E) = A := ((hav.cons1 Cv).cons1 Bv).2
  show Prog.Bounded w B (.letIn _ (.letIn _ (.letIn _ q))) E
  simp only [Prog.Bounded, e1, e2, e3]
  exact ⟨hc, hb, ha, (Prog'.bounded_append B q [A, Bv, Cv] E hq).mpr hqb⟩

theorem tm_callT1 {d : ℕ} (hq : Prog'.closed 1 q = true) (ta : Tm w L d a E) (ha : Val w E a A)
    (hqb : q.Bounded w (2 ^ (128 * L)) [A]) (hv : q.eval w [A] < 2 ^ L) :
    Tm w L 1 (callT1 q a) E := fun pre hp => by
  refine ⟨?_, by rw [denote_callT1v hq (ha.ext pre), one_mul]; exact hv⟩
  have e1 : (a (pre ++ E).length).eval w (pre ++ E) = A := (ha.ext pre).2
  show Prog.Bounded w _ (.letIn _ q) (pre ++ E)
  simp only [Prog.Bounded, e1]
  exact ⟨(ta pre hp).1, (Prog'.bounded_append _ q [A] (pre ++ E) hq).mpr hqb⟩

theorem tm_callT2 {da db : ℕ} (hq : Prog'.closed 2 q = true) (ta : Tm w L da a E)
    (ha : Val w E a A) (tb : Tm w L db b E) (hb : Val w E b Bv) (hBv : Bv < 2 ^ (32 * L))
    (hqb : q.Bounded w (2 ^ (128 * L)) [A, Bv]) (hv : q.eval w [A, Bv] < 2 ^ L) :
    Tm w L 1 (callT2 q a b) E := fun pre hp => by
  refine ⟨?_, by rw [denote_callT2v hq (ha.ext pre) (hb.ext pre), one_mul]; exact hv⟩
  refine bnd_callT2v hq (tb pre hp).1 (hb.ext pre) ?_ (ha.ext pre) hqb
  have := (ta (Bv :: pre) (Small.cons hBv hp)).1
  simpa using this

theorem tm_callT3 {da db dc : ℕ} (hq : Prog'.closed 3 q = true) (ta : Tm w L da a E)
    (ha : Val w E a A) (tb : Tm w L db b E) (hb : Val w E b Bv) (tc : Tm w L dc c E)
    (hc : Val w E c Cv) (hBv : Bv < 2 ^ (32 * L)) (hCv : Cv < 2 ^ (32 * L))
    (hqb : q.Bounded w (2 ^ (128 * L)) [A, Bv, Cv]) (hv : q.eval w [A, Bv, Cv] < 2 ^ L) :
    Tm w L 1 (callT3 q a b c) E := fun pre hp => by
  refine ⟨?_, by rw [denote_callT3v hq (ha.ext pre) (hb.ext pre) (hc.ext pre), one_mul]; exact hv⟩
  refine bnd_callT3v hq (tc pre hp).1 (hc.ext pre) ?_ (hb.ext pre) ?_ (ha.ext pre) hqb
  · have := (tb (Cv :: pre) (Small.cons hCv hp)).1
    simpa using this
  · have := (ta (Bv :: Cv :: pre) (Small.cons hBv (Small.cons hCv hp))).1
    simpa using this

end Call

/-! ### Numeric helpers

Powers of two above `(s + 2)^C`, and `LogspaceNetFamily.mul_succ_lt_pow`. -/

theorem pow_lt_two_pow_of {s C L : ℕ} (hL : (2 * C + 1) * (s.log2 + 1) ≤ L) :
    (s + 2) ^ C < 2 ^ L := by
  have h1 : s < 2 ^ (s.log2 + 1) := Nat.lt_log2_self
  have h2 : s + 2 ≤ 2 ^ (s.log2 + 2) := by
    have : 2 ^ (s.log2 + 2) = 2 * 2 ^ (s.log2 + 1) := by rw [pow_succ]; ring
    have : 1 ≤ 2 ^ (s.log2 + 1) := Nat.one_le_two_pow
    omega
  calc (s + 2) ^ C ≤ (2 ^ (s.log2 + 2)) ^ C := Nat.pow_le_pow_left h2 C
    _ = 2 ^ ((s.log2 + 2) * C) := (pow_mul _ _ _).symm
    _ < 2 ^ L := Nat.pow_lt_pow_right (by norm_num) (by nlinarith)

theorem mul_succ_lt_pow' (C s : ℕ) : C * (s + 1) < (s + 2) ^ (C + 1) := by
  have h1 : C + 1 ≤ (s + 2) ^ C :=
    (Nat.lt_two_pow_self (n := C)).trans_le (Nat.pow_le_pow_left (by omega) C)
  calc C * (s + 1) < (C + 1) * (s + 2) := by nlinarith
    _ ≤ (s + 2) ^ C * (s + 2) := Nat.mul_le_mul_right _ h1
    _ = (s + 2) ^ (C + 1) := (pow_succ _ _).symm

/-! ### The instance -/

variable (F : LogspaceNetFamily)

/-- **The network terms of a logspace family** at the size term `sT`: each accessor runs the
closed program of the family on its arguments and the size. -/
def famNetT (sT : Term) : NetT where
  MT := callT1 F.edgesP sT
  VT := callT1 F.vertsP sT
  uT a := callT2 F.endUP a sT
  wT a := callT2 F.endWP a sT
  degT a := callT2 F.degP a sT
  portT a b := callT3 F.portP a b sT
  evalT a b := callT3 F.funP a b sT

variable {F} {s : ℕ} {sT : Term}

/-- **The value contract** for a member, when `sT` has value `s`. -/
theorem famNet_acc (hm : F.Mem w s) (hs : Val w env sT s) :
    NetAcc (F.net w s) w env (famNetT F sT) where
  vM := (val_callT1 F.edgesP_closed hs).congr (F.edgesP_spec w s hm).1
  vV := (val_callT1 F.vertsP_closed hs).congr (F.vertsP_spec w s hm).1
  vu E hE a i ha hi := (val_callT2 F.endUP_closed ha (hs.up hE)).congr (by
    rw [(F.endUP_spec w s hm i hi).1, uN_of_lt hi])
  vw E hE a i ha hi := (val_callT2 F.endWP_closed ha (hs.up hE)).congr (by
    rw [(F.endWP_spec w s hm i hi).1, wN_of_lt hi])
  vdeg E hE a x ha hx := (val_callT2 F.degP_closed ha (hs.up hE)).congr (by
    rw [(F.degP_spec w s hm x hx).1, degN_of_lt hx])
  vport E hE a b x j ha hb hx hj := by
    rw [degN_of_lt hx] at hj
    exact (val_callT3 F.portP_closed ha hb (hs.up hE)).congr (by
      rw [(F.portP_spec w s hm x hx j hj).1, portN_of_lt hx hj])
  veval E hE a b x A ha hb hx hA := by
    rw [degN_of_lt hx] at hA
    refine (val_callT3 F.funP_closed ha hb (hs.up hE)).congr ?_
    rw [evalN_of_lt hx, ← (F.funP_spec w s hm x hx A hA).1, Int.toNat_natCast]

/-- The vertex functions of a member are nonnegative. -/
theorem famNet_evalNonneg (hm : F.Mem w s) : EvalNonneg (F.net w s) :=
  fun v x hx => (F.eval_mem w s hm v x hx).1

/-- **The tier contract** for a member, when `sT` has value `s` and tier `1`, at every budget
`L ≥ 16` with `(2 C + 3)(⌊log₂ s⌋ + 1) ≤ L`: every value arising in a program is at most
`(s + 2)^C ≤ 2^(128 L)`, and the results are below `(s + 2)^(C+1) < 2^L`. -/
theorem famNet_tiers (hm : F.Mem w s) (hs : Val w env sT s) (ts : Tm w L 1 sT env)
    (h16 : 16 ≤ L) (hL : (2 * F.C + 3) * (s.log2 + 1) ≤ L) :
    NetTiers (F.net w s) w L env (famNetT F sT) := by
  have hBL : (s + 2) ^ (F.C + 1) < 2 ^ L :=
    pow_lt_two_pow_of (by rw [show 2 * (F.C + 1) + 1 = 2 * F.C + 3 by ring]; exact hL)
  have hB0 : (s + 2) ^ F.C ≤ (s + 2) ^ (F.C + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hB128 : (s + 2) ^ F.C ≤ 2 ^ (128 * L) :=
    (hB0.trans hBL.le).trans (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hmono : ∀ {q : Prog} {env : List ℕ}, q.Bounded w ((s + 2) ^ F.C) env →
      q.Bounded w (2 ^ (128 * L)) env := fun h => Exact.bounded_mono hB128 _ _ h
  have hsL : s < 2 ^ L := lt_of_lt_of_le
    (lt_of_lt_of_le (by omega : s < s + 2) (Nat.le_self_pow (by omega) _)) hBL.le
  have h32 : ∀ {X : ℕ}, X < 2 ^ L → X < 2 ^ (32 * L) := fun h =>
    h.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hM : (F.net w s).M < 2 ^ L :=
    (F.edges_le w s hm).trans_lt ((mul_succ_lt_pow' F.C s).trans hBL)
  have hV : F.V w s < 2 ^ L := (F.verts_le w s hm).trans_lt (lt_of_le_of_lt hB0 hBL)
  have hdeg : ∀ v, ((F.net w s).ports v).length ≤ L := fun v => by
    have := F.deg_le w s hm v
    rw [← Nat.log2_eq_log_two] at this
    exact this.trans ((Nat.mul_le_mul_right _ (by omega)).trans hL)
  have hdeg2 : ∀ v, ((F.net w s).ports v).length < 2 ^ L := fun v =>
    (hdeg v).trans_lt Nat.lt_two_pow_self
  exact {
    hL := h16
    hΔ := hdeg
    tM := tm_callT1 F.edgesP_closed ts hs (hmono (F.edgesP_spec w s hm).2)
      (by rw [(F.edgesP_spec w s hm).1]; exact hM)
    tV := tm_callT1 F.vertsP_closed ts hs (hmono (F.vertsP_spec w s hm).2)
      (by rw [(F.vertsP_spec w s hm).1]; exact hV)
    tu := fun E hE a i ha ta hi => by
      obtain ⟨hv, hb⟩ := F.endUP_spec w s hm i hi
      exact tm_callT2 F.endUP_closed ta ha (ts.ext hE) (hs.extE hE) (h32 hsL) (hmono hb)
        (by rw [hv]; exact (Fin.isLt _).trans hV)
    tw := fun E hE a i ha ta hi => by
      obtain ⟨hv, hb⟩ := F.endWP_spec w s hm i hi
      exact tm_callT2 F.endWP_closed ta ha (ts.ext hE) (hs.extE hE) (h32 hsL) (hmono hb)
        (by rw [hv]; exact (Fin.isLt _).trans hV)
    tdeg := fun E hE a x ha ta hx => by
      obtain ⟨hv, hb⟩ := F.degP_spec w s hm x hx
      exact tm_callT2 F.degP_closed ta ha (ts.ext hE) (hs.extE hE) (h32 hsL) (hmono hb)
        (by rw [hv]; exact hdeg2 _)
    tport := fun E hE a b x j ha ta hb tb hx hj => by
      rw [degN_of_lt hx] at hj
      obtain ⟨hv, hq⟩ := F.portP_spec w s hm x hx j hj
      exact tm_callT3 F.portP_closed ta ha tb hb (ts.ext hE) (hs.extE hE)
        (h32 (hj.trans (hdeg2 _))) (h32 hsL) (hmono hq) (by rw [hv]; exact (Fin.isLt _).trans hM)
    teval := fun E hE a b x A ha ta hb tb hx hA => by
      rw [degN_of_lt hx] at hA
      obtain ⟨hv, hq⟩ := F.funP_spec w s hm x hx A hA
      have hfv : F.funP.eval w [x, A, s] ≤ (s + 2) ^ F.C := by
        have := (F.eval_mem w s hm ⟨x, hx⟩
          (List.ofFn fun j : Fin ((F.net w s).ports ⟨x, hx⟩).length => A.testBit j)
          List.length_ofFn).2
        rw [← hv] at this
        exact_mod_cast this
      have hA' : A < 2 ^ L := hA.trans_le (Nat.pow_le_pow_right (by norm_num) (hdeg _))
      exact tm_callT3 F.funP_closed ta ha tb hb (ts.ext hE) (hs.extE hE) (h32 hA') (h32 hsL)
        (hmono hq) (hfv.trans_lt (hB0.trans_lt hBL)) }

end Cslib.Complexity.NtimeDspace.Cube.Num
