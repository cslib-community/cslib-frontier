/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.BudgetTerm
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.CodeTerm
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.EntryNum

/-!
# The entry and range states as terms (Lemma 6.4)

Program terms (`ProgTerm.Term`) for the numeric functions of `EntryNum.lean`, with value lemmas
(`val_*`, in the stable form `Num.Val` of `CodeTerm.lean`) and tier lemmas (`tm_*`, `Tame.lean`).

`CodeTerm.lean` states values as `Num.Val w env t n` (stable, with value `n`), `BudgetTerm.lean`
as `Cross.Exact.Val w t env n` (value `n` in every extension); the two are equivalent
(`val_iff_exactVal`, `Val.toExact`, `Cross.Exact.Val.toNum`).

## Main definitions

* `tOnesE`, `hdE`, `tlE`, `stGetT`: list access on codes of `NatList.enc`, without binders.
* `sizeE`, `consE`, `encE`: writing list codes, without binders.
* `zzSubT`, `swapT`, `unpackT`, `labOkT`: the label-code transducers `zzSub`, `swapN`, `unpackN`,
  `labOkN`.
* `trRootT`: the code of the root transport state of a rectangle factor (`trRootN`).
* `argLabT`: the code of a label of an argument code (`argLabN`).

## Main results

* `val_stGetT`, `tm_stGetT`: an entry of a list code; its tier is that of the code.
* `val_encE`, `tm_consE`, `tm_encE`: a list code has the tier of any bound on its value
  (at most `29`), whatever the tiers of its entries.
* `val_swapT`, `tm_swapT`, `val_unpackT`, `tm_unpackT`, `val_labOkT`, `tm_labOkT`: on label codes
  of at most `B ≤ L` bits, the transducers have tier `1`.
* `val_trRootT`, `tm_trRootT`, `val_argLabT`.

The terms of the state-level functions of `EntryNum.lean` (`psiN`, `factorGN`, `factorN`,
`clChildN`,
`entTagN`, `entChildN`, `rngChildN`, …) are compositions of these with the terms of
`BudgetTerm.lean` (`budT`, `argOffT`, `sliceT`, `xiWidT`, `childT`, `choiceValidT`, `orientT`,
`diagT`, `digT`, `packLT`, `nFacT`) and are not yet written here.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Cube.Num

open NtimeDspace.ProgTerm NtimeDspace.ProgTerm.Term SumProduct

variable {w : List Bool} {env : List ℕ} {L : ℕ}

/-! ### The two value conventions -/

/-- `Num.Val` (stable with value `v`) is `Cross.Exact.Val` (value `v` in every extension). -/
theorem val_iff_exactVal {t : Term} {v : ℕ} : Val w env t v ↔ Cross.Exact.Val w t env v :=
  ⟨fun h extra => (h.1 extra).trans h.2, fun h => ⟨fun extra => (h extra).trans h.eq.symm, h.eq⟩⟩

theorem Val.toExact {t : Term} {v : ℕ} (h : Val w env t v) : Cross.Exact.Val w t env v :=
  val_iff_exactVal.mp h

theorem _root_.Cslib.Complexity.NtimeDspace.Cross.Exact.Val.toNum {t : Term} {v : ℕ}
    (h : Cross.Exact.Val w t env v) :
    Val w env t v := val_iff_exactVal.mpr h

/-- `2 ^ e` from the value of the exponent. -/
theorem t_pow2v {e : Term} {E d de : ℕ} (hv : Val w env e E) (he : Tm w L de e env) (hde : de ≤ 32)
    (hE : E < d * L) (hd : d ≤ 32) (hL : 2 ≤ L) : Tm w L d (pow2 e) env :=
  t_pow2 he hde (fun pre _ => by rw [(hv.ext pre).2]; exact hE) hd hL

/-! ### Lists -/

/-- The number of trailing ones of `e` (`tOnesF`). -/
def tOnesE (e : Term) : Term :=
  foldT e (const 0) fun acc i =>
    ite (lt acc i) acc (ite (lt i acc) acc (ite (bit e i) (add i (const 1)) acc))

/-- The head of a list code (`hdF`). -/
def hdE (e : Term) : Term := mod (div e (pow2 (add (tOnesE e) (const 1)))) (pow2 (tOnesE e))

/-- The tail of a list code (`tlF`). -/
def tlE (e : Term) : Term := div e (pow2 (add (add (tOnesE e) (tOnesE e)) (const 1)))

/-- Entry `k` of a list code (`stGet`). -/
def stGetT (n : Term) (k : ℕ) : Term := hdE (tlE^[k] n)

section Lists

variable {e : Term} {E : ℕ}

theorem val_tOnesE (he : Val w env e E) : Val w env (tOnesE e) (tOnesF E) := by
  have := val_foldT (f := fun acc i =>
      ite (lt acc i) acc (ite (lt i acc) acc (ite (bit e i) (add i (const 1)) acc)))
    (step := tOnesStep E) he (val_const 0) fun pre x k _ =>
      (val_ite (val_lt (val_acc _ x k) (val_idx _ x k)) (val_acc _ x k)
        (val_ite (val_lt (val_idx _ x k) (val_acc _ x k)) (val_acc _ x k)
          (val_ite (val_bit (he.at2 pre x k) (val_idx _ x k))
            (val_add (val_idx _ x k) (val_const 1)) (val_acc _ x k)))).congr (by
        unfold tOnesStep
        by_cases h1 : x < k
        · simp [h1]
        · by_cases h2 : k < x
          · simp [h1, h2]
          · cases E.testBit k <;> simp [h1, h2])
  exact this

theorem val_hdE (he : Val w env e E) : Val w env (hdE e) (hdF E) :=
  val_mod (val_div he (val_pow2 (val_add (val_tOnesE he) (val_const 1)))) (val_pow2 (val_tOnesE he))

theorem val_tlE (he : Val w env e E) : Val w env (tlE e) (tlF E) :=
  val_div he (val_pow2 (val_add (val_add (val_tOnesE he) (val_tOnesE he)) (val_const 1)))

theorem val_tlE_iter (he : Val w env e E) : ∀ k, Val w env (tlE^[k] e) (tlF^[k] E)
  | 0 => he
  | k + 1 => by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact val_tlE (val_tlE_iter he k)

theorem val_stGetT (he : Val w env e E) (k : ℕ) : Val w env (stGetT e k) (stGet E k) :=
  val_hdE (val_tlE_iter he k)

theorem tOnesF_le (E : ℕ) : tOnesF E ≤ E := by
  have : ∀ m, (List.range m).foldl (tOnesStep E) 0 ≤ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil, tOnesStep]
      split_ifs <;> omega
  exact this E

theorem tm_tOnesE {de : ℕ} (he : Val w env e E) (te : Tm w L de e env) (hde1 : 1 ≤ de)
    (hde : de + 1 ≤ 32) (hL : 1 ≤ L) : Tm w L (de + 1) (tOnesE e) env := by
  refine tm_val (d' := de + 1) ?_ (val_tOnesE he) ?_
  · refine tm_foldT te (by omega) ((t_const (k := 0) (by positivity)).mono (by omega))
      (fun E' hE x i (hx : Tm w L (de + 1) x E') (hi : Tm w L de i E') => ?_) hde
    have hei := te.ext hE
    have i1 : Tm w L (de + 1) (add i (const 1)) E' := (t_add hi (t_one hL) hL (by omega)).mono
        (by omega)
    have i2 := t_ite (t_bit hei hi hL) i1 hx
    have i3 := t_ite (t_lt hi hx hL) hx i2
    exact (t_ite (t_lt hx hi hL) hx i3).mono (by omega)
  · have h1 := (te [] Small.nil).2
    rw [List.nil_append, he.2] at h1
    exact (tOnesF_le E).trans_lt (h1.trans_le (Nat.pow_le_pow_right (by norm_num)
      (Nat.mul_le_mul_right _ (by omega))))

/-- The tier of the head and the tail of the code of a nonempty list: that of the code. -/
theorem tm_hdE_tlE {de : ℕ} {x : ℕ} {l : List ℕ} (he : Val w env e (NatList.enc (x :: l)))
    (te : Tm w L de e env) (hde1 : 1 ≤ de) (hde : de + 3 ≤ 32) (hL : 2 ≤ L) :
    Tm w L de (hdE e) env ∧ Tm w L de (tlE e) env := by
  have t1 := tm_tOnesE he te hde1 (by omega) (by omega)
  have hv := val_tOnesE he
  rw [tOnesF_enc_cons] at hv
  have hlt : NatList.enc (x :: l) < 2 ^ (de * L) := by
    have h1 := (te [] Small.nil).2; rwa [List.nil_append, he.2] at h1
  have hsz : 2 * x.size + 1 < (de + 1) * L := by
    have h2 := NatList.two_pow_le_enc_cons x l
    have : 2 * x.size + 1 < de * L := (Nat.pow_lt_pow_iff_right (by norm_num)).mp (h2.trans_lt hlt)
    rw [Nat.add_mul, one_mul]; omega
  refine ⟨t_mod_left (t_div te (t_pow2v (d := de + 1) (val_add hv (val_const 1))
    (t_add t1 (t_one (by omega)) (by omega) (by omega)) (by omega) (by omega) (by omega)
        (by omega)))
      (t_pow2v (d := de + 1) hv t1 (by omega) (by omega) (by omega) (by omega)),
    t_div te (t_pow2v (d := de + 1) (val_add (val_add hv hv) (val_const 1))
      (t_add (t_add t1 t1 (by omega) (by omega)) (t_one (by omega)) (by omega) (by omega))
      (by omega) (by omega) (by omega) (by omega))⟩

/-- **The tier of an entry of a list code** is at most that of the code. -/
theorem tm_stGetT {de : ℕ} {l : List ℕ} (he : Val w env e (NatList.enc l)) (te : Tm w L de e env)
    (hde1 : 1 ≤ de) (hde : de + 3 ≤ 32) (hL : 2 ≤ L) :
    ∀ k, k < l.length → Tm w L de (stGetT e k) env := by
  induction l generalizing e with
  | nil => intro k hk; simp at hk
  | cons x l ih =>
    intro k hk
    obtain ⟨th, tt⟩ := tm_hdE_tlE he te hde1 hde hL
    rcases k with _ | k
    · exact th
    · have vt := val_tlE he
      rw [tlF_enc_cons] at vt
      have := ih vt tt (k := k) (by simpa using hk)
      simpa [stGetT, Function.iterate_succ_apply] using this

end Lists

/-! ### Label codes -/

/-- `zzSub a b` (`zz (a - b)`). -/
def zzSubT (a b : Term) : Term :=
  ite (lt b (add a (const 1))) (mul (const 2) (sub a b)) (sub (mul (const 2) (sub b a)) (const 1))

theorem val_zzSubT {a b : Term} {A B : ℕ} (ha : Val w env a A) (hb : Val w env b B) :
    Val w env (zzSubT a b) (zzSub A B) :=
  (val_ite (val_lt hb (val_add ha (val_const 1))) (val_mul (val_const 2) (val_sub ha hb))
    (val_sub (val_mul (val_const 2) (val_sub hb ha)) (val_const 1))).congr (by
      unfold zzSub; by_cases h : B ≤ A
      · simp [show B < A + 1 by omega, h]
      · simp [show ¬ B < A + 1 by omega, h])

theorem tm_zzSubT {a b : Term} {da db : ℕ} (ta : Tm w L da a env) (tb : Tm w L db b env)
    (hL : 2 ≤ L) (hd : max da db + 1 ≤ 128) : Tm w L (max da db + 1) (zzSubT a b) env := by
  have t2 : Tm w L 1 (const 2) env := t_small (by norm_num) hL
  have h1 : Tm w L (1 + da) (mul (const 2) (sub a b)) env := t_mul t2 (t_sub ta tb) (by omega)
  have h2 : Tm w L (1 + db) (sub (mul (const 2) (sub b a)) (const 1)) env :=
    t_sub (t_mul t2 (t_sub tb ta) (by omega)) (t_one (by omega))
  exact (t_ite (t_lt tb (t_add ta (t_one (by omega)) (by omega) (by omega)) (by omega))
    (h1.mono (d' := max da db + 1) (by omega)) (h2.mono (d' := max da db + 1) (by omega))).mono
    (by omega)

theorem lcode_lt_pow {B : ℕ} {l : Label} (h : LB B l) (hBL : B ≤ L) : lcode l < 2 ^ (1 * L) := by
  unfold LB at h
  refine (ofBits_lt _).trans_le (Nat.pow_le_pow_right (by norm_num) ?_)
  rw [List.length_append]; omega

/-- The code of `swapLabel` (`swapN`). -/
def swapT (B c : Term) : Term :=
  add (div c (pow2 (msEndT B c (const 0))))
    (mul (pow2 (sub (msEndT B c (msEndT B c (const 0))) (msEndT B c (const 0))))
      (mod c (pow2 (msEndT B c (const 0)))))

variable {B c Lt s : Term} {Bv cv Lv sv : ℕ}

theorem val_swapT (hB : Val w env B Bv) (hc : Val w env c cv) : Val w env (swapT B c)
    (swapN Bv cv) := by
  have e1 := val_msEndT hB hc (val_const 0)
  exact val_add (val_div hc (val_pow2 e1))
    (val_mul (val_pow2 (val_sub (val_msEndT hB hc e1) e1)) (val_mod hc (val_pow2 e1)))

theorem tm_swapT {l : Label} (hB : Val w env B Bv) (hc : Val w env c (lcode l))
    (tB : Tm w L 1 B env)
    (tc : Tm w L 1 c env) (hl : LB Bv l) (hL : 4 ≤ L) (hBL : Bv ≤ L) : Tm w L 1 (swapT B c)
        env := by
  have t0 : Tm w L 1 (const 0) env := t_small (by norm_num) (by omega)
  have e1 := val_msEndT hB hc (val_const 0)
  have e2 := val_msEndT hB hc e1
  have m1 := tm_msEndT hB hc (val_const 0) tB tc t0 le_rfl (by norm_num) hL hBL
  have m2 := tm_msEndT hB hc e1 tB tc m1 (by norm_num) (by norm_num) hL hBL
  have h1 := msEnd_lcode hl
  have h2 := msEnd2_lcode hl
  unfold LB at hl
  rw [h1] at e2
  have p1 := t_pow2v e1 m1 (by norm_num) (d := 2) (by rw [h1]; omega) (by norm_num) (by omega)
  have p2 := t_pow2v (val_sub e2 e1) (t_sub m2 m1) (by norm_num) (d := 2) (by rw [h1, h2]; omega)
    (by norm_num) (by omega)
  refine tm_val (t_add (t_div tc p1) (t_mul p2 (t_mod_left tc p1) (by norm_num)) (by omega)
    (by norm_num)) (val_swapT hB hc) ?_
  rw [swapN_lcode hl]
  exact lcode_lt_pow (B := Bv) (by unfold LB swapLabel; simp only; omega) hBL

/-- The multiplicities of the types `L k + s` in the multiset code at `q` (for `unpackN`). -/
def unpackCntT (B c q Lt s : Term) (k : Term) : Term := countT B c q (add (mul Lt k) s)

/-- **Unpacking stream `s`** on a label code (`unpackN`). -/
def unpackT (B Lt s c : Term) : Term :=
  add (ocCodeT B (topT B c (const 0)) (unpackCntT B c (const 0) Lt s))
    (mul (pow2 (ocLenT B (topT B c (const 0)) (unpackCntT B c (const 0) Lt s)))
      (ocCodeT B (topT B c (msEndT B c (const 0))) (unpackCntT B c (msEndT B c (const 0)) Lt s)))

theorem valF1_unpackCntT {q : Term} {qv : ℕ} (hB : Val w env B Bv) (hc : Val w env c cv)
    (hq : Val w env q qv) (hLt : Val w env Lt Lv) (hs : Val w env s sv) :
    ValF1 w (unpackCntT B c q Lt s) (fun k => countN Bv cv qv (Lv * k + sv)) env :=
  fun pre _ _ hy => val_countT (hB.ext pre) (hc.ext pre) (hq.ext pre)
    (val_add (val_mul (hLt.ext pre) hy) (hs.ext pre))

theorem val_unpackT (hB : Val w env B Bv) (hLt : Val w env Lt Lv) (hs : Val w env s sv)
    (hc : Val w env c cv) : Val w env (unpackT B Lt s c) (unpackN Bv Lv sv cv) := by
  have e1 := val_msEndT hB hc (val_const 0)
  exact val_add (val_ocCodeT hB (val_topT hB hc (val_const 0))
      (valF1_unpackCntT hB hc (val_const 0) hLt hs))
    (val_mul (val_pow2 (val_ocLenT hB (val_topT hB hc (val_const 0))
      (valF1_unpackCntT hB hc (val_const 0) hLt hs)))
      (val_ocCodeT hB (val_topT hB hc e1) (valF1_unpackCntT hB hc e1 hLt hs)))

theorem ocLen_le (W X : ℕ) (C : ℕ → ℕ) : (msOfCount W X C).2 ≤ W + 1 := by
  have hI := ocInv_foldl (W := W) (cnt := C) (List.range X)
    ((appendN W 0 0 (ocNum X C + 1)).1, (appendN W 0 0 (ocNum X C + 1)).2, 0)
    ⟨appendN_lt (by simp), appendN_snd_le W 0 0 _⟩
  exact hI.2

theorem tmV1_unpackCntT {q : Term} {qv dq dLt ds : ℕ} (hB : Val w env B Bv) (hc : Val w env c cv)
    (hq : Val w env q qv) (hLt : Val w env Lt Lv) (hs : Val w env s sv) (tB : Tm w L 1 B env)
    (tc : Tm w L 1 c env) (tq : Tm w L dq q env) (tLt : Tm w L dLt Lt env) (ts : Tm w L ds s env)
    (hdq1 : 1 ≤ dq) (hdq : dq ≤ 64) (hd : dLt + 4 + ds ≤ 100) (hL : 4 ≤ L) (hBL : Bv ≤ L) :
    TmV1 w L (unpackCntT B c q Lt s) 4 env := by
  intro E hE y Y hy ty
  have hE' := hE
  obtain ⟨pre, -, rfl⟩ := hE
  exact (tm_countT (hB.ext pre) (hc.ext pre) (hq.ext pre)
    (val_add (val_mul (hLt.ext pre) hy) (hs.ext pre)) (tB.ext hE') (tc.ext hE') (tq.ext hE')
    (t_add (t_mul (tLt.ext hE') ty (by omega)) (ts.ext hE') (by omega) (by omega))
    hdq1 hdq hL hBL).mono (by norm_num)

theorem tm_unpackT {l : Label} {Φ dLt ds : ℕ} (hB : Val w env B Bv) (hLt : Val w env Lt Lv)
    (hs : Val w env s sv) (hc : Val w env c (lcode l)) (tB : Tm w L 1 B env)
        (tLt : Tm w L dLt Lt env)
    (ts : Tm w L ds s env) (tc : Tm w L 1 c env) (hd : dLt + ds ≤ 90) (hsL : sv < Lv)
    (hl : labelWt l ≤ Φ) (hΦ : codeWidth Φ + 2 ≤ Bv) (hL : 4 ≤ L) (hBL : Bv ≤ L) :
    Tm w L 1 (unpackT B Lt s c) env := by
  have t0 : Tm w L 1 (const 0) env := t_small (by norm_num) (by omega)
  have e1 := val_msEndT hB hc (val_const 0)
  have m1 := tm_msEndT hB hc (val_const 0) tB tc t0 le_rfl (by norm_num) hL hBL
  have X1 := val_topT hB hc (val_const 0)
  have tX1 := tm_topT hB hc (val_const 0) tB tc t0 le_rfl (by norm_num) hL hBL
  have X2 := val_topT hB hc e1
  have tX2 := tm_topT hB hc e1 tB tc m1 (by norm_num) (by norm_num) hL hBL
  have C1 := valF1_unpackCntT hB hc (val_const 0) hLt hs
  have C2 := valF1_unpackCntT hB hc e1 hLt hs
  have TC1 := tmV1_unpackCntT hB hc (val_const 0) hLt hs tB tc t0 tLt ts le_rfl (by norm_num)
    (by omega) hL hBL
  have TC2 := tmV1_unpackCntT hB hc e1 hLt hs tB tc m1 tLt ts (by norm_num) (by norm_num)
    (by omega) hL hBL
  have o1 := tm_ocCodeT hB X1 C1 tB tX1 TC1 (by norm_num) hL hBL
  have n1 := tm_ocLenT hB X1 C1 tB tX1 TC1 (by norm_num) hL hBL
  have o2 := tm_ocCodeT hB X2 C2 tB tX2 TC2 (by norm_num) hL hBL
  have p := t_pow2v (d := 2) (val_ocLenT hB X1 C1) n1 (by norm_num)
    (by have := ocLen_le Bv (topN Bv (lcode l) 0) (fun k => countN Bv (lcode l) 0 (Lv * k + sv)); omega)
    (by norm_num) (by omega)
  refine tm_val (t_add o1 (t_mul p o2 (by norm_num)) (by omega) (by norm_num))
      (val_unpackT hB hLt hs hc) ?_
  rw [unpackN_lcode hsL hl hΦ]
  exact lcode_lt_pow (lb_of_le ((labelWt_unpack_le _ _ _).trans hl) hΦ) hBL

/-! ### Validity of a packed label -/

/-- The step of the scan of the first multiset: a type `≡ 0 (mod L)` other than `0` kills. -/
def labOkStep1 (Lt : Term) (a e _μ : Term) : Term :=
  ite (eqT (mod e Lt) (const 0)) (ite (lt (const 0) e) (const 0) a) a

/-- The step of the scan of the second multiset: a type `≡ 0 (mod L)` kills. -/
def labOkStep2 (Lt : Term) (a e _μ : Term) : Term := ite (eqT (mod e Lt) (const 0)) (const 0) a

/-- **Validity of a packed label** by scanning its code (`labOkN`), as `0`/`1`. -/
def labOkT (B Lt c : Term) : Term :=
  ite (eqT (msFoldT (labOkStep1 Lt) (const 1) B c (const 0)) (const 1))
    (eqT (msFoldT (labOkStep2 Lt) (const 1) B c (msEndT B c (const 0))) (const 1)) (const 0)

theorem valF3_labOkStep1 (hLt : Val w env Lt Lv) :
    ValF3 w (labOkStep1 Lt) (fun a e _ => if e % Lv = 0 ∧ e ≠ 0 then 0 else a) env :=
  fun pre _ _ _ X Y _ hx hy _ => (val_ite (val_eqT (val_mod hy (hLt.ext pre)) (val_const 0))
    (val_ite (val_lt (val_const 0) hy) (val_const 0) hx) hx).congr (by
      by_cases h1 : Y % Lv = 0 <;> by_cases h2 : Y = 0 <;> simp [h1, h2, Nat.pos_iff_ne_zero])

theorem valF3_labOkStep2 (hLt : Val w env Lt Lv) :
    ValF3 w (labOkStep2 Lt) (fun a e _ => if e % Lv = 0 then 0 else a) env :=
  fun pre _ _ _ X Y _ hx hy _ => (val_ite (val_eqT (val_mod hy (hLt.ext pre)) (val_const 0))
    (val_const 0) hx).congr (by by_cases h1 : Y % Lv = 0 <;> simp [h1])

theorem val_labOkT (hB : Val w env B Bv) (hLt : Val w env Lt Lv) (hc : Val w env c cv) :
    Val w env (labOkT B Lt c) (ind (labOkN Bv Lv cv)) := by
  have f1 := val_msFoldT (valF3_labOkStep1 hLt) (val_const 1) hB hc (val_const 0)
  have f2 := val_msFoldT (valF3_labOkStep2 hLt) (val_const 1) hB hc (val_msEndT hB hc (val_const 0))
  refine (val_ite (val_eqT f1 (val_const 1)) (val_eqT f2 (val_const 1)) (val_const 0)).congr ?_
  unfold labOkN ind
  split_ifs <;> simp_all

theorem tm_labOkT {dLt : ℕ} (hB : Val w env B Bv) (hLt : Val w env Lt Lv) (hc : Val w env c cv)
    (tB : Tm w L 1 B env) (tLt : Tm w L dLt Lt env) (tc : Tm w L 1 c env) (hL : 4 ≤ L)
    (hBL : Bv ≤ L) : Tm w L 1 (labOkT B Lt c) env := by
  have t0 : Tm w L 1 (const 0) env := t_small (by norm_num) (by omega)
  have t1 : Tm w L 1 (const 1) env := t_one (by omega)
  have e1 := val_msEndT hB hc (val_const 0)
  have m1 := tm_msEndT hB hc (val_const 0) tB tc t0 le_rfl (by norm_num) hL hBL
  have hG1 : ∀ a e μ : ℕ, a < 2 ^ (1 * L) → e < 2 ^ (2 * L + 3) → μ < 2 ^ (L + 1) →
      (if e % Lv = 0 ∧ e ≠ 0 then 0 else a) < 2 ^ (1 * L) := fun a _ _ ha _ _ => by
    split_ifs
    · positivity
    · exact ha
  have hG2 : ∀ a e μ : ℕ, a < 2 ^ (1 * L) → e < 2 ^ (2 * L + 3) → μ < 2 ^ (L + 1) →
      (if e % Lv = 0 then 0 else a) < 2 ^ (1 * L) := fun a _ _ ha _ _ => by
    split_ifs
    · positivity
    · exact ha
  have g1 : TmV3 w L (labOkStep1 Lt) 1 env := fun E hE x y z _ _ _ _ _ _ tx ty _ => by
    have t0' : Tm w L 1 (const 0) E := t_small (by norm_num) (by omega)
    exact (t_ite (t_eqT' (t_mod_left ty (tLt.ext hE)) t0' (by omega))
      (t_ite (t_lt t0' ty (by omega)) t0' tx) tx).mono (by omega)
  have g2 : TmV3 w L (labOkStep2 Lt) 1 env := fun E hE x y z _ _ _ _ _ _ tx ty _ => by
    have t0' : Tm w L 1 (const 0) E := t_small (by norm_num) (by omega)
    exact (t_ite (t_eqT' (t_mod_left ty (tLt.ext hE)) t0' (by omega)) t0' tx).mono (by omega)
  have f1 := tm_msFoldT_cl (valF3_labOkStep1 hLt) g1 (by norm_num) hG1 (val_const 1) t1 hB hc
    (val_const 0) tB tc t0 le_rfl (by norm_num) hL hBL
  have f2 := tm_msFoldT_cl (valF3_labOkStep2 hLt) g2 (by norm_num) hG2 (val_const 1) t1 hB hc e1
    tB tc m1 (by norm_num) (by norm_num) hL hBL
  exact (t_ite (t_eqT' f1 t1 (by omega)) (t_eqT' f2 t1 (by omega)) t0).mono (by omega)

/-! ### Writing list codes -/

/-- The bit length (`Nat.size`), without binders. -/
def sizeE (x : Term) : Term := foldT x (const 0) fun acc i => ite (bit x i) (add i (const 1)) acc

/-- The cons of list codes (`consF`), without binders. -/
def consE (x l : Term) : Term :=
  add (add (sub (pow2 (sizeE x)) (const 1)) (mul (pow2 (add (sizeE x) (const 1))) x))
    (mul (pow2 (add (add (sizeE x) (sizeE x)) (const 1))) l)

/-- The code of a list of terms. -/
def encE : List Term → Term
  | [] => const 1
  | x :: l => consE x (encE l)

section Write

variable {x l : Term} {X Lc : ℕ}

theorem val_sizeE (hx : Val w env x X) : Val w env (sizeE x) X.size := by
  have := val_foldT (f := fun acc i => ite (bit x i) (add i (const 1)) acc) (step := sizeStep X) hx
    (val_const 0) fun pre a k _ => (val_ite (val_bit (hx.at2 pre a k) (val_idx _ a k))
      (val_add (val_idx _ a k) (val_const 1)) (val_acc _ a k)).congr (by
        unfold sizeStep; cases X.testBit k <;> simp)
  rw [← sizeF, sizeF_eq] at this
  exact this

theorem val_consE (hx : Val w env x X) (hl : Val w env l Lc) : Val w env (consE x l)
    (consF X Lc) := by
  have hs := val_sizeE hx
  refine (val_add (val_add (val_sub (val_pow2 hs) (val_const 1)) (val_mul (val_pow2
    (val_add hs (val_const 1))) hx)) (val_mul (val_pow2 (val_add (val_add hs hs) (val_const 1)))
        hl)).congr ?_
  rw [consF, sizeF_eq]

theorem val_encE : ∀ {ts : List Term} {vs : List ℕ}, List.Forall₂ (fun t v => Val w env t v) ts vs →
    Val w env (encE ts) (NatList.enc vs)
  | [], [], _ => val_const 1
  | _ :: _, _ :: _, List.Forall₂.cons h hs => by
    rw [encE, ← consF_enc]; exact val_consE h (val_encE hs)

theorem size_lt_tier {X d : ℕ} (h : X < 2 ^ (d * L)) : X.size ≤ d * L := Nat.size_le.mpr h

theorem tm_sizeE {dx : ℕ} (hx : Val w env x X) (tx : Tm w L dx x env) (hdx1 : 1 ≤ dx)
    (hdx : dx + 1 ≤ 32) (hL : 1 ≤ L) : Tm w L (dx + 1) (sizeE x) env := by
  refine tm_val (d' := dx + 1) ?_ (val_sizeE hx) ?_
  · refine tm_foldT tx (by omega) ((t_const (k := 0) (by positivity)).mono (by omega))
      (fun E' hE a i (ha : Tm w L (dx + 1) a E') (hi : Tm w L dx i E') => ?_) hdx
    have i1 : Tm w L (dx + 1) (add i (const 1)) E' := (t_add hi (t_one hL) hL (by omega)).mono
        (by omega)
    exact (t_ite (t_bit (tx.ext hE) hi hL) i1 ha).mono (by omega)
  · have h1 := (tx [] Small.nil).2
    rw [List.nil_append, hx.2] at h1
    have := size_lt_tier h1
    have : dx * L < 2 ^ ((dx + 1) * L) :=
      (Nat.lt_two_pow_self).trans_le (Nat.pow_le_pow_right (by norm_num) (by nlinarith))
    omega

/-- **The tier of a cons**, from a bound on its value (`d ≤ 29`); the arguments may have any tier.
-/
theorem tm_consE {dx dl d : ℕ} (hx : Val w env x X) (hl : Val w env l Lc) (tx : Tm w L dx x env)
    (tl : Tm w L dl l env) (hl1 : 1 ≤ Lc) (hd1 : 1 ≤ d) (hd : d ≤ 29) (hL : 2 ≤ L)
    (hv : consF X Lc < 2 ^ (d * L)) : Tm w L d (consE x l) env := by
  obtain ⟨g1, g2, -, g4, -⟩ := consF_ge X Lc hl1
  rw [sizeF_eq] at g2 g4
  have h2l : 2 ^ (X.size + X.size + 1) ≤ 2 ^ (X.size + X.size + 1) * Lc := Nat.le_mul_of_pos_right _
      hl1
  have hlc : Lc ≤ 2 ^ (X.size + X.size + 1) * Lc := Nat.le_mul_of_pos_left _ (by positivity)
  have tx' := tm_val tx hx (g1.trans_lt hv)
  have tl' := tm_val tl hl ((hlc.trans g4).trans_lt hv)
  have hexp : X.size + X.size + 1 < d * L := (Nat.pow_lt_pow_iff_right (by norm_num)).mp
      (g2.trans_lt hv)
  have hs := val_sizeE hx
  have ts := tm_sizeE hx tx' hd1 (by omega) (by omega)
  have one : ∀ {E : List ℕ}, Tm w L 1 (const 1) E := t_one (by omega)
  have p0 := t_pow2v (d := d) hs ts (by omega) (by omega) (by omega) hL
  have p1 := t_pow2v (d := d) (val_add hs (val_const 1)) (t_add ts one (by omega) (by omega))
    (by omega) (by omega) (by omega) hL
  have p2 := t_pow2v (d := d) (val_add (val_add hs hs) (val_const 1))
    (t_add (t_add ts ts (by omega) (by omega)) one (by omega) (by omega)) (by omega) (by omega)
        (by omega) hL
  exact tm_val (t_add (t_add (t_sub p0 one) (t_mul p1 tx' (by omega)) (by omega) (by omega))
    (t_mul p2 tl' (by omega)) (by omega) (by omega)) (val_consE hx hl) hv

/-- **The tier of a list code**, from a bound on its value (`d ≤ 29`); entries of any tier. -/
theorem tm_encE {d : ℕ} (hd1 : 1 ≤ d) (hd : d ≤ 29) (hL : 2 ≤ L) : ∀ {ts : List Term} {vs : List ℕ},
    List.Forall₂ (fun t v => Val w env t v ∧ ∃ dt, Tm w L dt t env) ts vs →
    NatList.enc vs < 2 ^ (d * L) → Tm w L d (encE ts) env
  | [], [], _, _ => ((t_one (by omega) : Tm w L 1 (const 1) env)).mono hd1
  | _ :: _, v :: vs, List.Forall₂.cons ⟨hv, _, ht⟩ hs, hlt => by
    have hl := val_encE (List.Forall₂.imp (fun _ _ h => h.1) hs)
    have hlt' : NatList.enc vs < 2 ^ (d * L) := (NatList.enc_le_enc_cons v vs).trans_lt hlt
    rw [encE]
    exact tm_consE hv hl ht (tm_encE hd1 hd hL hs hlt') (NatList.enc_pos vs) hd1 hd hL
      (by rw [consF_enc]; exact hlt)

end Write

/-! ### The root transport state of a rectangle factor -/

/-- The code of the root transport state from the codes of its labels (`trRootN`). -/
def trRootT (B : Term) (up : Bool) (xC yC mC zc : Term) : Term :=
  encE [const 7, const up.toNat, xC, yC, mC, const 0,
    add (add (cardT B xC (const 0)) (cardT B yC (const 0)))
      (if up then cardT B mC (msEndT B mC (const 0)) else cardT B mC (const 0)),
    encE [div xC (pow2 (msEndT B xC (const 0))), div yC (pow2 (msEndT B yC (const 0))),
      if up then mod mC (pow2 (msEndT B mC (const 0))) else div mC (pow2 (msEndT B mC (const 0)))],
          zc]

section TrRoot

variable {xC yC mC zc : Term} {xv yv mv zv : ℕ}

theorem val_trRootT (up : Bool) (hB : Val w env B Bv) (hx : Val w env xC xv) (hy : Val w env yC yv)
    (hm : Val w env mC mv) (hz : Val w env zc zv) :
    Val w env (trRootT B up xC yC mC zc) (trRootN Bv up xv yv mv zv) := by
  have e0 : ∀ {c : Term} {cv : ℕ}, Val w env c cv → Val w env (msEndT B c (const 0))
      (msEnd Bv cv 0) :=
    fun h => val_msEndT hB h (val_const 0)
  have inner : ∀ up' : Bool, Val w env (encE [div xC (pow2 (msEndT B xC (const 0))),
      div yC (pow2 (msEndT B yC (const 0))),
      if up' then mod mC (pow2 (msEndT B mC (const 0))) else div mC (pow2 (msEndT B mC (const 0)))])
      (NatList.enc [xv / 2 ^ msEnd Bv xv 0, yv / 2 ^ msEnd Bv yv 0,
        if up' then mv % 2 ^ msEnd Bv mv 0 else mv / 2 ^ msEnd Bv mv 0]) := fun up' => by
    refine val_encE (.cons (val_div hx (val_pow2 (e0 hx))) (.cons (val_div hy (val_pow2 (e0 hy)))
      (.cons ?_ .nil)))
    cases up'
    · exact val_div hm (val_pow2 (e0 hm))
    · exact val_mod hm (val_pow2 (e0 hm))
  have len : Val w env (add (add (cardT B xC (const 0)) (cardT B yC (const 0)))
      (if up then cardT B mC (msEndT B mC (const 0)) else cardT B mC (const 0)))
      (cardN Bv xv 0 + cardN Bv yv 0 + if up then cardN Bv mv (msEnd Bv mv 0) else cardN Bv mv
          0) := by
    refine val_add (val_add (val_cardT hB hx (val_const 0)) (val_cardT hB hy (val_const 0))) ?_
    cases up
    · exact val_cardT hB hm (val_const 0)
    · exact val_cardT hB hm (e0 hm)
  exact val_encE (.cons (val_const 7) (.cons (val_const _) (.cons hx (.cons hy (.cons hm
    (.cons (val_const 0) (.cons len (.cons (inner up) (.cons hz .nil)))))))))

/-- **The tier of the root transport code**, from a bound on its value; the label codes are codes of
labels of at most `B ≤ L` bits. -/
theorem tm_trRootT (up : Bool) {x y m : Label} {dz d : ℕ} (hB : Val w env B Bv)
    (hx : Val w env xC (lcode x)) (hy : Val w env yC (lcode y)) (hm : Val w env mC (lcode m))
    (hz : Val w env zc zv) (tB : Tm w L 1 B env) (tx : Tm w L 1 xC env) (ty : Tm w L 1 yC env)
    (tm : Tm w L 1 mC env) (tz : Tm w L dz zc env) (lx : LB Bv x) (ly : LB Bv y) (lm : LB Bv m)
    (hd1 : 1 ≤ d) (hd : d ≤ 29) (hL : 4 ≤ L) (hBL : Bv ≤ L)
    (hv : trRootN Bv up (lcode x) (lcode y) (lcode m) zv < 2 ^ (d * L)) :
    Tm w L d (trRootT B up xC yC mC zc) env := by
  have t0 : Tm w L 1 (const 0) env := t_small (by norm_num) (by omega)
  have pw : ∀ {c : Term} {l : Label}, Val w env c (lcode l) → Tm w L 1 c env → LB Bv l →
      Tm w L 2 (pow2 (msEndT B c (const 0))) env := fun hc tc hl =>
    t_pow2v (val_msEndT hB hc (val_const 0)) (tm_msEndT hB hc (val_const 0) tB tc t0 le_rfl
      (by norm_num) hL hBL) (by norm_num) (by rw [msEnd_lcode hl]; unfold LB at hl; omega)
          (by norm_num)
      (by omega)
  have cd : ∀ {c q : Term} {cv qv dq : ℕ}, Val w env c cv → Val w env q qv → Tm w L 1 c env →
      Tm w L dq q env → 1 ≤ dq → dq ≤ 64 → Tm w L 3 (cardT B c q) env :=
    fun hc hq tc tq h1 h2 => tm_cardT hB hc hq tB tc tq h1 h2 hL hBL
  have m1 := tm_msEndT hB hm (val_const 0) tB tm t0 le_rfl (by norm_num) hL hBL
  have key : ∀ (a b c d' e f g I z : ℕ), I ≤ NatList.enc [a, b, c, d', e, f, g, I, z] := by
    intro a b c d' e f g I z
    calc I ≤ NatList.enc [I, z] := NatList.le_enc_cons _ _
      _ ≤ NatList.enc [g, I, z] := NatList.enc_le_enc_cons _ _
      _ ≤ NatList.enc [f, g, I, z] := NatList.enc_le_enc_cons _ _
      _ ≤ NatList.enc [e, f, g, I, z] := NatList.enc_le_enc_cons _ _
      _ ≤ NatList.enc [d', e, f, g, I, z] := NatList.enc_le_enc_cons _ _
      _ ≤ NatList.enc [c, d', e, f, g, I, z] := NatList.enc_le_enc_cons _ _
      _ ≤ NatList.enc [b, c, d', e, f, g, I, z] := NatList.enc_le_enc_cons _ _
      _ ≤ NatList.enc [a, b, c, d', e, f, g, I, z] := NatList.enc_le_enc_cons _ _
  unfold trRootT
  refine tm_encE hd1 hd (by omega) ?_ (by unfold trRootN at hv; exact hv)
  refine .cons ⟨val_const 7, 1, t_const (lt_of_lt_of_le (by norm_num : 7 < 2 ^ 4)
      (Nat.pow_le_pow_right (by norm_num) hL))⟩ (.cons ⟨val_const _, 1,
    t_const (lt_of_le_of_lt (show up.toNat ≤ 1 by cases up <;> simp)
        (Nat.one_lt_two_pow (by omega)))⟩ (.cons ⟨hx, 1, tx⟩
    (.cons ⟨hy, 1, ty⟩ (.cons ⟨hm, 1, tm⟩ (.cons ⟨val_const 0, 1, t0⟩ (.cons ⟨?_, ?_⟩
    (.cons ⟨?_, ?_⟩ (.cons ⟨hz, dz, tz⟩ .nil))))))))
  · refine val_add (val_add (val_cardT hB hx (val_const 0)) (val_cardT hB hy (val_const 0))) ?_
    cases up
    · exact val_cardT hB hm (val_const 0)
    · exact val_cardT hB hm (val_msEndT hB hm (val_const 0))
  · have hA := t_add (cd hx (val_const 0) tx t0 le_rfl (by norm_num))
      (cd hy (val_const 0) ty t0 le_rfl (by norm_num)) (by omega) (by norm_num)
    have hC : Tm w L 3 (if up then cardT B mC (msEndT B mC (const 0)) else cardT B mC (const 0))
        env := by
      cases up
      · exact cd hm (val_const 0) tm t0 le_rfl (by norm_num)
      · exact cd hm (val_msEndT hB hm (val_const 0)) tm m1 (by norm_num) (by norm_num)
    exact ⟨_, t_add hA hC (by omega) (by norm_num)⟩
  · refine val_encE (.cons (val_div hx (val_pow2 (val_msEndT hB hx (val_const 0))))
      (.cons (val_div hy (val_pow2 (val_msEndT hB hy (val_const 0)))) (.cons ?_ .nil)))
    cases up
    · exact val_div hm (val_pow2 (val_msEndT hB hm (val_const 0)))
    · exact val_mod hm (val_pow2 (val_msEndT hB hm (val_const 0)))
  · refine ⟨d, tm_encE hd1 hd (by omega) (.cons ⟨val_div hx (val_pow2 (val_msEndT hB hx
      (val_const 0))), 1, t_div tx (pw hx tx lx)⟩ (.cons ⟨val_div hy (val_pow2 (val_msEndT hB hy
      (val_const 0))), 1, t_div ty (pw hy ty ly)⟩
          (.cons (b := if up then lcode m % 2 ^ msEnd Bv (lcode m) 0
      else lcode m / 2 ^ msEnd Bv (lcode m) 0) ⟨?_, 1, ?_⟩ .nil))) ?_⟩
    · cases up
      · exact val_div hm (val_pow2 (val_msEndT hB hm (val_const 0)))
      · exact val_mod hm (val_pow2 (val_msEndT hB hm (val_const 0)))
    · cases up
      · exact t_div tm (pw hm tm lm)
      · exact t_mod_left tm (pw hm tm lm)
    · exact (key _ _ _ _ _ _ _ _ _).trans_lt hv

end TrRoot

/-! ### Labels of argument codes -/

/-- **The code of the label at `u`** of an argument code `x` of node `v` (`argLabN`). -/
def argLabT (arT qT fwT v x u : Term) : Term :=
  ite (lt v qT) (ite (lt u qT) (ite (eqT u v) (const 3)
    (ite (lt (const 0) (budT arT qT fwT v u))
      (ite (eqT (validT (budT arT qT fwT v u) (codeWidthT (budT arT qT fwT v u))
          (mod (divPowT (const 2) x (argOffT arT qT fwT v u))
              (pow2 (codeWidthT (budT arT qT fwT v u)))))
          (const 1))
        (mod (divPowT (const 2) x (argOffT arT qT fwT v u))
            (pow2 (codeWidthT (budT arT qT fwT v u))))
        (const 3)) (const 3))) (const 3)) (const 3)

theorem val_argLabT {arT qT fwT v x u : Term} {ar q fw V X U : ℕ} (har : Val w env arT ar)
    (hq : Val w env qT q) (hfw : Val w env fwT fw) (hv : Val w env v V) (hx : Val w env x X)
    (hu : Val w env u U) : Val w env (argLabT arT qT fwT v x u) (argLabN ar q fw V X U) := by
  have hb := (val_budT har.toExact hq.toExact hfw.toExact hv.toExact hu.toExact).toNum
  have ho := (val_argOffT har.toExact hq.toExact hfw.toExact hv.toExact hu.toExact).toNum
  have hW := val_codeWidthT hb
  have hf := val_mod ((val_divPowT (Cross.Exact.val_const 2 env) hx.toExact ho.toExact).toNum)
      (val_pow2 hW)
  have hval := val_validT hb hW hf
  refine (val_ite (val_lt hv hq) (val_ite (val_lt hu hq) (val_ite (val_eqT hu hv) (val_const 3)
    (val_ite (val_lt (val_const 0) hb) (val_ite (val_eqT hval (val_const 1)) hf (val_const 3))
      (val_const 3))) (val_const 3)) (val_const 3)).congr ?_
  unfold argLabN
  split_ifs <;> simp_all

end Cslib.Complexity.NtimeDspace.Cube.Num
