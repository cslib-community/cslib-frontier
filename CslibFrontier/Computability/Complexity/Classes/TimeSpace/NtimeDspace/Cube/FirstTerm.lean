/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.BudgetTerm
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.NetTerms

/-!
# The first clique as terms: the budget array and the leaf factors (Lemma 4.3 (c))

The machine of Lemma 6.4 needs, at the first clique, its budget array and the leaf factors
`Setup.factor0 v args f` of its table entries. Both are computed here by terms from the network
accessors (`NetT`, `NetTerms.lean`), with the labels of an entry read from their codes by the
streaming terms of `CodeTerm.lean` (`validT`, `countT`, `cardT`, `msEndT`) and the budgets and
code offsets read from the budget array by the terms of `BudgetTerm.lean` (`budT`, `argOffT`,
`bCodeWidthT`).

The values use `Num.Val` of `CodeTerm.lean` (stable, with a value); `valE`/`valN` translate to and
from `Cross.Exact.Val` of `BudgetTerm.lean`.

## Inputs

`FirstT` bundles the terms: the network `N`, `K`, `q = 2K`, the field width `fw`, the budget array,
the node `v` and the argument code `args`. `FIn` states their values (`NetAcc` for the network),
`FTiers` their tiers at budget `L`: the network contract `NetTiers` (so `L ≥ 16`), tier `1` for
`K`, `q`, `fw`, `v`, tier at most `32` for the array and the argument code, `1 ≤ K`, `v < 2K`,
`fw < L`, and every code width `codeWidth (budAt K ar fw v n)`, `n < 2K`, at most `L` (`hcw`).

## Main definitions

* `firstDigT`, `firstArrT`: the digits and the budget array of the first clique (`firstDigit`,
  `arrN (2K) fw (extN (firstBudget G K))`, the layout of `BudgetNum.lean`).
* `cwT`, `slotT`: the width and the code of the label to node `n` in the argument code.
* `bitT` (`bitAt`, the bit `decEnc` of a label, from its code), `isEncT` (`IsEncC`, the test
  `IsEnc`), `allLtT` (a bounded `∀`).
* `vbitT`, `argAT`, `vfacT`: the vertex factors; `tbitT`, `efacT`: the test factors; `enc0T`: the
  encoding test; `factor0T`: the leaf factor.

## Main results

* `val_firstArrT`, `tm_firstArrT`: the budget array, of tier `d` when `4K²·fw ≤ d·L`, `d ≤ 32`.
* `val_factor0T`, `tm_factor0T`: the leaf factor has value `factor0C` and tier `1`.
* `factor0T_eq`: for a network with nonnegative vertex functions, the value is `Setup.factor0`.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Cube.Num

open Finset NtimeDspace.ProgTerm NtimeDspace.ProgTerm.Term NtimeDspace.Cross

variable {w : List Bool} {L : ℕ} {env : List ℕ}

/-! ### Helpers -/

theorem valE {t : Term} {n : ℕ} (h : Val w env t n) : Cross.Exact.Val w t env n :=
  fun extra => (h.1 extra).trans h.2

theorem valN {t : Term} {n : ℕ} (h : Cross.Exact.Val w t env n) : Val w env t n :=
  ⟨h.stable, h.eq⟩

theorem valN_divPowT {x T i : Term} {X Tv I : ℕ} (hx : Val w env x X) (hT : Val w env T Tv)
    (hi : Val w env i I) : Val w env (divPowT x T i) (Tv / X ^ I) :=
  Val.of_denote _ fun pre => by
    rw [divPowT_denote _ _ _ _ (hx.ext pre).1, (hx.ext pre).2, (hT.ext pre).2, (hi.ext pre).2]

/-- A branch taken only under a condition needs a value only under it. -/
theorem val_ite_cond {c t e : Term} {C T E : ℕ} (hc : Val w env c C) (ht : 0 < C → Val w env t T)
    (he : ¬ 0 < C → Val w env e E) : Val w env (ite c t e) (if 0 < C then T else E) :=
  Val.of_denote _ fun pre => by
    rw [denote_ite, (hc.ext pre).2]
    by_cases h : 0 < C
    · rw [ite_eq_left h, ite_eq_left h]; exact ((ht h).ext pre).2
    · rw [ite_eq_right h, ite_eq_right h]; exact ((he h).ext pre).2

theorem of_pos_ind {P : Prop} [Decidable P] (h : 0 < (if P then 1 else 0)) : P := by
  by_contra hP; simp [hP] at h

theorem ite_and_toNat (P Q : Prop) [Decidable P] [Decidable Q] :
    (if 0 < (if P then 1 else 0) then (if Q then 1 else 0) else 0) = (decide (P ∧ Q)).toNat := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]

theorem ite_toNat_eq (b c : Bool) : (if b.toNat = c.toNat then 1 else 0) = if b =
    c then 1 else 0 := by
  cases b <;> cases c <;> simp

theorem ite_decide_toNat (P : Prop) [Decidable P] : (if P then 1 else 0) = (decide P).toNat := by
  by_cases h : P <;> simp [h]

theorem max_add_le {a b : ℕ} (ha : a ≤ 28) (hb : b ≤ 28) : max a b + 3 ≤ 32 := by
  rw [Nat.max_def]; split_ifs <;> omega

theorem sum_toNat_lt (b : ℕ → Bool) (n : ℕ) : ∑ j ∈ range n, (b j).toNat * 2 ^ j < 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, pow_succ]
    have : (b n).toNat ≤ 1 := Bool.toNat_le _
    have : (b n).toNat * 2 ^ n ≤ 2 ^ n :=
      (Nat.mul_le_mul_right _ this).trans (by rw [one_mul])
    omega

theorem vgroupC_lt {V : ℕ} (G : EdgeNet ℤ (Fin V)) {K : ℕ} (hK : 1 ≤ K) (x : ℕ) :
    vgroupC G K x < K := by
  unfold vgroupC; omega

theorem tgroupC_lt {V : ℕ} (G : EdgeNet ℤ (Fin V)) {K : ℕ} (hK : 1 ≤ K) (e : ℕ) :
    tgroupC G K e < K := Nat.mod_lt _ (by omega)

/-- A bounded universal quantifier over `0/1` tests: `1` if every test `k < n` is `1`. -/
def allLtT (n : Term) (test : Term → Term) : Term :=
  lt (sumT n fun k => sub (const 1) (test k)) (const 1)

theorem val_allLtT {n : Term} {test : Term → Term} {Nv : ℕ} {P : ℕ → Prop} [DecidablePred P]
    (hn : Val w env n Nv) (ht : ∀ (pre : List ℕ) (x k : ℕ), k < Nv →
      Val w (x :: k :: (pre ++ env)) (test (lvl (pre ++ env).length)) (if P k then 1 else 0)) :
    Val w env (allLtT n test) (if ∀ k < Nv, P k then 1 else 0) := by
  have hs := val_sumT (body := fun k => sub (const 1) (test k))
    (g := fun k => 1 - if P k then 1 else 0) hn fun pre x k hk =>
    val_sub (val_const 1) (ht pre x k hk)
  refine (val_lt hs (val_const 1)).congr ?_
  have key : (∑ k ∈ range Nv, (1 - if P k then 1 else 0) < 1) ↔ ∀ k < Nv, P k := by
    rw [Nat.lt_one_iff, Finset.sum_eq_zero_iff]
    refine ⟨fun h k hk => ?_, fun h k hk => ?_⟩
    · have := h k (mem_range.mpr hk)
      by_contra hp
      simp only [hp, ite_false] at this
      omega
    · simp only [h k (mem_range.mp hk), ite_true, Nat.sub_self]
  by_cases hall : ∀ k < Nv, P k
  · rw [ite_eq_left (key.mpr hall), ite_eq_left hall]
  · rw [ite_eq_right (mt key.mp hall), ite_eq_right hall]

theorem tm_allLtT {n : Term} {test : Term → Term} {Nv dn dt : ℕ} (hn : Val w env n Nv)
    (tn : Tm w L dn n env) (hdn : dn + 1 ≤ 32) (hL : 16 ≤ L)
    (ht : ∀ E, Ext L E env → ∀ y k, Val w E y k → k < Nv → Tm w L dn y E → Tm w L dt (test y) E) :
    Tm w L 1 (allLtT n test) env :=
  t_lt (tm_sumTb (db := 1) hn tn (fun E hE y k hy hk ty =>
    t_sub (tcst (k := 1) (by norm_num) le_rfl hL) (ht E hE y k hy hk ty)) (by omega) hdn)
    (tcst (by norm_num) le_rfl hL) (by omega)

/-! ### The inputs -/

/-- The terms of the first clique: the network, `K`, `q = 2K`, the field width, the budget array,
the node `v` and the argument code. -/
structure FirstT where
  N : NetT
  KT : Term
  qT : Term
  fwT : Term
  arT : Term
  vT : Term
  argsT : Term

variable {V : ℕ} {G : EdgeNet ℤ (Fin V)} {F : FirstT} {K fw ar v args : ℕ}

variable (G) in
/-- The values of the inputs. -/
structure FIn (w : List Bool) (env : List ℕ) (F : FirstT) (K fw ar v args : ℕ) : Prop where
  hA : NetAcc G w env F.N
  vK : Val w env F.KT K
  vq : Val w env F.qT (2 * K)
  vfw : Val w env F.fwT fw
  var : Val w env F.arT ar
  vv : Val w env F.vT v
  vargs : Val w env F.argsT args

variable (G) in
/-- The tiers of the inputs at budget `L`, and the size conditions. -/
structure FTiers (w : List Bool) (L : ℕ) (env : List ℕ) (F : FirstT) (K fw ar v : ℕ) : Prop where
  hT : NetTiers G w L env F.N
  tK : Tm w L 1 F.KT env
  tq : Tm w L 1 F.qT env
  tfw : Tm w L 1 F.fwT env
  tar : Tm w L 32 F.arT env
  tv : Tm w L 1 F.vT env
  targs : Tm w L 32 F.argsT env
  hK1 : 1 ≤ K
  hv : v < 2 * K
  hfw : fw < L
  hcw : ∀ n < 2 * K, codeWidth (budAt K ar fw v n) ≤ L

theorem FIn.up (h : FIn G w env F K fw ar v args) {E : List ℕ} (hE : Above env E) :
    FIn G w E F K fw ar v args :=
  ⟨h.hA.up hE, h.vK.up hE, h.vq.up hE, h.vfw.up hE, h.var.up hE, h.vv.up hE, h.vargs.up hE⟩

theorem FTiers.up (t : FTiers G w L env F K fw ar v) {E : List ℕ} (hE : Ext L E env) :
    FTiers G w L E F K fw ar v :=
  ⟨t.hT.up hE, t.tK.ext hE, t.tq.ext hE, t.tfw.ext hE, t.tar.ext hE, t.tv.ext hE, t.targs.ext hE,
    t.hK1, t.hv, t.hfw, t.hcw⟩

theorem FTiers.hL (t : FTiers G w L env F K fw ar v) : 16 ≤ L := t.hT.hL

/-- The inputs in the format of `BudgetTerm.lean` (no grid: `g = 1`, `i = 0`). -/
theorem FIn.inp (h : FIn G w env F K fw ar v args) :
    Inp w env F.arT F.qT F.fwT (const 1) (const 0) ar (2 * K) fw 1 0 :=
  ⟨valE h.var, valE h.vq, valE h.vfw, Cross.Exact.val_const 1 env, Cross.Exact.val_const 0 env⟩

theorem FTiers.bt (t : FTiers G w L env F K fw ar v) :
    Tiers w L env F.arT F.qT F.fwT (const 1) (const 0) fw 1 :=
  ⟨t.tar, t.tq, t.tfw, tcst (by norm_num) le_rfl t.hL, tcst (by norm_num) (by norm_num) t.hL, t.hL,
    t.hfw, one_pos⟩

/-! ### Labels of an argument code -/

/-- The width of the code of the label to node `n`. -/
def cwT (F : FirstT) (n : Term) : Term := bCodeWidthT (budT F.arT F.qT F.fwT F.vT n)

/-- The code of the label to node `n` in the argument code (`slotN`). -/
def slotT (F : FirstT) (n : Term) : Term :=
  mod (divPowT (const 2) F.argsT (argOffT F.arT F.qT F.fwT F.vT n)) (pow2 (cwT F n))

/-- Bit `p` of the string of the label to node `n` (`bitAt`), from its code. -/
def bitT (F : FirstT) (n p : Term) : Term :=
  ite (eqT (validT (budT F.arT F.qT F.fwT F.vT n) (cwT F n) (slotT F n)) (const 1))
    (lt (const 0) (countT (cwT F n) (slotT F n) (const 0) p)) (const 0)

/-- The encoding test `IsEnc b` of the label to node `n` (`IsEncC`), from its code. -/
def isEncT (F : FirstT) (n b : Term) : Term :=
  ite (eqT (validT (budT F.arT F.qT F.fwT F.vT n) (cwT F n) (slotT F n)) (const 1))
    (ite (allLtT b fun p => eqT (add (countT (cwT F n) (slotT F n) (const 0) p)
        (countT (cwT F n) (slotT F n) (msEndT (cwT F n) (slotT F n) (const 0)) p)) (const 1))
      (eqT (add (cardT (cwT F n) (slotT F n) (const 0))
        (cardT (cwT F n) (slotT F n) (msEndT (cwT F n) (slotT F n) (const 0)))) b) (const 0))
    (eqT b (const 0))

variable {nT pT bT : Term} {n p b : ℕ}

theorem val_budT' (h : FIn G w env F K fw ar v args) (hn : Val w env nT n) :
    Val w env (budT F.arT F.qT F.fwT F.vT nT) (budAt K ar fw v n) :=
  valN (val_budT (valE h.var) (valE h.vq) (valE h.vfw) (valE h.vv) (valE hn))

theorem tm_budT' {dn : ℕ} (t : FTiers G w L env F K fw ar v) (h : FIn G w env F K fw ar v args)
    (tn : Tm w L dn nT env) (hdn : dn ≤ 28) : Tm w L 1 (budT F.arT F.qT F.fwT F.vT nT) env :=
  tm_budT t.bt (valE h.vfw) t.tv tn (max_add_le (by norm_num) hdn)

theorem val_cwT (h : FIn G w env F K fw ar v args) (hn : Val w env nT n) :
    Val w env (cwT F nT) (codeWidth (budAt K ar fw v n)) :=
  valN (val_bCodeWidthT (valE (val_budT' h hn)))

theorem tm_cwT {dn : ℕ} (t : FTiers G w L env F K fw ar v) (h : FIn G w env F K fw ar v args)
    (hn : Val w env nT n) (tn : Tm w L dn nT env) (hdn : dn ≤ 28) (hn2 : n < 2 * K) :
    Tm w L 1 (cwT F nT) env :=
  tm_val (tm_bCodeWidthT (tm_budT' t h tn hdn) t.hL) (val_cwT h hn) (lt_tier_one (t.hcw n hn2))

theorem val_slotT (h : FIn G w env F K fw ar v args) (hn : Val w env nT n) :
    Val w env (slotT F nT) (slotN K ar fw v args n) :=
  val_mod (valN_divPowT (val_const 2) h.vargs
    (valN (val_argOffT (valE h.var) (valE h.vq) (valE h.vfw) (valE h.vv) (valE hn))))
    (val_pow2 (val_cwT h hn))

theorem tm_slotT {dn : ℕ} (t : FTiers G w L env F K fw ar v) (h : FIn G w env F K fw ar v args)
    (hn : Val w env nT n) (tn : Tm w L dn nT env) (hdn : dn ≤ 24) (hn2 : n < 2 * K) :
    Tm w L 2 (slotT F nT) env := by
  have hL := t.hL
  have hcw := t.hcw n hn2
  exact t_mod (t_divPowT (tcst (k := 2) (by norm_num) le_rfl hL) t.targs
      (tm_argOffT h.inp t.bt t.tv tn (by norm_num) (by omega)) (by omega) le_rfl)
    (t_pow2 (tm_cwT t h hn tn (by omega) hn2) (by norm_num)
      (fun pre _ => by rw [((val_cwT h hn).ext pre).2]; omega) (by norm_num) (by omega)) Pos.pow2'

theorem val_bitT (h : FIn G w env F K fw ar v args) (hn : Val w env nT n) (hp : Val w env pT p) :
    Val w env (bitT F nT pT) (bitAt K ar fw v args n p).toNat :=
  (val_ite (val_eqT (val_validT (val_budT' h hn) (val_cwT h hn) (val_slotT h hn)) (val_const 1))
    (val_lt (val_const 0) (val_countT (val_cwT h hn) (val_slotT h hn) (val_const 0) hp))
    (val_const 0)).congr (ite_and_toNat _ _)

theorem tm_bitT {dn dp : ℕ} (t : FTiers G w L env F K fw ar v) (h : FIn G w env F K fw ar v args)
    (hn : Val w env nT n) (tn : Tm w L dn nT env) (hdn : dn ≤ 24) (hn2 : n < 2 * K)
    (hp : Val w env pT p) (tp : Tm w L dp pT env) : Tm w L 1 (bitT F nT pT) env := by
  have hL := t.hL
  have hcw := t.hcw n hn2
  exact tm_ite (t_eqT' (tm_validT (val_budT' h hn) (val_cwT h hn) (val_slotT h hn)
      (tm_budT' t h tn (by omega)) (tm_cwT t h hn tn (by omega) hn2) (tm_slotT t h hn tn hdn hn2)
      (by norm_num) (by omega) hcw) (tcst (by norm_num) le_rfl hL) (by omega))
    (t_lt (tcst (by norm_num) le_rfl hL) (tm_countT (val_cwT h hn) (val_slotT h hn) (val_const 0) hp
      (tm_cwT t h hn tn (by omega) hn2) (tm_slotT t h hn tn hdn hn2)
      (tcst (k := 0) (by norm_num) le_rfl hL) tp le_rfl (by norm_num) (by omega) hcw) (by omega))
    (tcst (by norm_num) le_rfl hL)

theorem val_isEncT (h : FIn G w env F K fw ar v args) (hn : Val w env nT n) (hb : Val w env bT b) :
    Val w env (isEncT F nT bT)
      (if IsEncC (budAt K ar fw v n) b (slotN K ar fw v args n) then 1 else 0) := by
  have hW := val_cwT h hn
  have hc := val_slotT h hn
  have hq := val_msEndT hW hc (val_const 0)
  have hall := val_allLtT (P := fun p => countN (codeWidth (budAt K ar fw v n))
      (slotN K ar fw v args n) 0 p + countN (codeWidth (budAt K ar fw v n)) (slotN K ar fw v args n)
        (msEnd (codeWidth (budAt K ar fw v n)) (slotN K ar fw v args n) 0) p = 1)
    (test := fun p => eqT (add (countT (cwT F nT) (slotT F nT) (const 0) p)
        (countT (cwT F nT) (slotT F nT) (msEndT (cwT F nT) (slotT F nT) (const 0)) p)) (const 1))
    hb fun pre x k _ => val_eqT (val_add (val_countT (hW.at2 pre x k) (hc.at2 pre x k)
      (val_const 0) (val_idx _ x k)) (val_countT (hW.at2 pre x k) (hc.at2 pre x k) (hq.at2 pre x k)
      (val_idx _ x k))) (val_const 1)
  refine (val_ite (val_eqT (val_validT (val_budT' h hn) hW hc) (val_const 1))
    (val_ite hall (val_eqT (val_add (val_cardT hW hc (val_const 0)) (val_cardT hW hc hq)) hb)
      (val_const 0)) (val_eqT hb (val_const 0))).congr ?_
  rw [ite_ind, ite_and_toNat, ← ite_decide_toNat]
  by_cases hv : validN (budAt K ar fw v n) (codeWidth (budAt K ar fw v n))
      (slotN K ar fw v args n) = 1
  · rw [ite_eq_left hv]
    refine if_congr ?_ rfl rfl
    unfold IsEncC
    rw [ite_eq_left hv]
  · rw [ite_eq_right hv]
    refine if_congr ?_ rfl rfl
    unfold IsEncC
    rw [ite_eq_right hv]

theorem tm_isEncT {dn db : ℕ} (t : FTiers G w L env F K fw ar v) (h : FIn G w env F K fw ar v args)
    (hn : Val w env nT n) (tn : Tm w L dn nT env) (hdn : dn ≤ 24) (hn2 : n < 2 * K)
    (hb : Val w env bT b) (tb : Tm w L db bT env) (hdb : db + 1 ≤ 32) :
    Tm w L 1 (isEncT F nT bT) env := by
  have hL := t.hL
  have hcw := t.hcw n hn2
  have hW := val_cwT h hn
  have hc := val_slotT h hn
  have tW := tm_cwT t h hn tn (by omega) hn2
  have tc := tm_slotT t h hn tn hdn hn2
  have hq := val_msEndT hW hc (val_const 0)
  have tq := tm_msEndT hW hc (val_const 0) tW tc (tcst (k := 0) (by norm_num) le_rfl hL) le_rfl
    (by norm_num) (by omega) hcw
  refine tm_ite (t_eqT' (tm_validT (val_budT' h hn) hW hc (tm_budT' t h tn (by omega)) tW tc
      (by norm_num) (by omega) hcw) (tcst (by norm_num) le_rfl hL) (by omega))
    (tm_ite (tm_allLtT (dt := 1) hb tb hdb hL fun E hE y k hy _ ty => ?_)
      (t_eqT' (tm_add (d := 4) (tm_cardT hW hc (val_const 0) tW tc
        (tcst (k := 0) (by norm_num) le_rfl hL) le_rfl (by norm_num) (by omega) hcw)
        (tm_cardT hW hc hq tW tc tq (by norm_num) (by norm_num) (by omega) hcw)
        (by norm_num) (by norm_num) (by norm_num) (by omega)) tb (by omega))
      (tcst (by norm_num) le_rfl hL))
    (t_eqT' tb (tcst (by norm_num) le_rfl hL) (by omega))
  have hE' := ext_above hE
  exact t_eqT' (tm_add (d := 3)
    (tm_countT (hW.up hE') (hc.up hE') (val_const 0) hy (tW.ext hE) (tc.ext hE)
      (tcst (k := 0) (by norm_num) le_rfl hL) ty le_rfl (by norm_num) (by omega) hcw)
    (tm_countT (hW.up hE') (hc.up hE') (hq.up hE') hy (tW.ext hE) (tc.ext hE) (tq.ext hE) ty
      (by norm_num) (by norm_num) (by omega) hcw)
    (by norm_num) (by norm_num) (by norm_num) (by omega)) (tcst (by norm_num) le_rfl hL) (by omega)

/-! ### The encoding test of an entry -/

/-- The encoding test of the entry of node `v` (factor `0`). -/
def enc0T (F : FirstT) : Term :=
  ite (lt F.vT F.KT)
    (allLtT F.KT fun τ => isEncT F (add F.KT τ) (widthT F.N F.KT F.vT τ))
    (allLtT F.KT fun j => isEncT F j (widthT F.N F.KT j (sub F.vT F.KT)))

theorem val_enc0T (h : FIn G w env F K fw ar v args) :
    Val w env (enc0T F) (if v < K then
      (if ∀ τ < K, IsEncC (budAt K ar fw v (K + τ)) (widthC G K v τ) (slotN K ar fw v args (K + τ))
        then 1 else 0)
    else
      (if ∀ j < K, IsEncC (budAt K ar fw v j) (widthC G K j (v - K)) (slotN K ar fw v args j)
        then 1 else 0)) := by
  refine (val_ite (val_lt h.vv h.vK)
    (val_allLtT h.vK fun pre x k _ => ?_) (val_allLtT h.vK fun pre x k _ => ?_)).congr (ite_ind _ _)
  · have h' := h.up (above_at2 pre x k)
    exact val_isEncT h' (val_add h'.vK (val_idx _ x k))
      (val_widthT h'.hA h'.vK h'.vv (val_idx _ x k))
  · have h' := h.up (above_at2 pre x k)
    exact val_isEncT h' (val_idx _ x k)
      (val_widthT h'.hA h'.vK (val_idx _ x k) (val_sub h'.vv h'.vK))

theorem tm_enc0T (t : FTiers G w L env F K fw ar v) (h : FIn G w env F K fw ar v args) :
    Tm w L 1 (enc0T F) env := by
  have hL := t.hL
  refine tm_ite (t_lt t.tv t.tK (by omega))
    (tm_allLtT (dt := 1) h.vK t.tK (by norm_num) hL fun E hE y k hy hk ty => ?_)
    (tm_allLtT (dt := 1) h.vK t.tK (by norm_num) hL fun E hE y k hy hk ty => ?_)
  · have h' := h.up (ext_above hE)
    have t' := t.up hE
    exact tm_isEncT t' h' (val_add h'.vK hy) (tm_add (d := 2) t'.tK ty le_rfl le_rfl (by norm_num)
      (by omega)) (by norm_num) (by omega) (val_widthT h'.hA h'.vK h'.vv hy)
      (tm_widthT h'.hA t'.hT h'.vK t'.tK t.hK1 t'.tv ty) (by norm_num)
  · have h' := h.up (ext_above hE)
    have t' := t.up hE
    exact tm_isEncT t' h' hy ty (by norm_num) (by omega)
      (val_widthT h'.hA h'.vK hy (val_sub h'.vv h'.vK))
      (tm_widthT h'.hA t'.hT h'.vK t'.tK t.hK1 ty (t_sub t'.tv t'.tK)) (by norm_num)

/-! ### The vertex factors -/

/-- The bit carried by port `j` of vertex `x` (`vbitC`). -/
def vbitT (F : FirstT) (x j : Term) : Term :=
  bitT F (add F.KT (tgroupT F.N F.KT (F.N.portT x j)))
    (hePosT F.N F.KT F.vT (tgroupT F.N F.KT (F.N.portT x j)) (F.N.portT x j)
      (eqT (F.N.wT (F.N.portT x j)) x))

/-- The number whose bit `j` is the bit carried by port `j` of `x` (`argA`). -/
def argAT (F : FirstT) (x : Term) : Term := sumT (F.N.degT x) fun j => mul (vbitT F x j) (pow2 j)

/-- The factor of vertex `x` in the entry of vertex group `v`. -/
def vfacT (F : FirstT) (x : Term) : Term :=
  ite (eqT (vgroupT F.N F.KT x) F.vT) (F.N.evalT x (argAT F x)) (const 1)

variable {xT jT : Term} {x j : ℕ}

theorem val_vbitT (h : FIn G w env F K fw ar v args) (hx : Val w env xT x) (hxV : x < V)
    (hj : Val w env jT j) (hjd : j < degN G x) :
    Val w env (vbitT F xT jT) (vbitC G K ar fw v args x j).toNat := by
  have hp := h.hA.vport _ (Above.refl _) _ _ _ _ hx hj hxV hjd
  have hpM := portN_lt hxV hjd
  have htg := val_tgroupT h.hA h.vK hp hpM
  exact val_bitT h (val_add h.vK htg) (val_hePosT h.hA h.vK h.vv htg hp hpM
    ((val_eqT (h.hA.vw _ (Above.refl _) _ _ hp hpM) hx).congr (ite_decide_toNat _)))

theorem tm_vbitT (t : FTiers G w L env F K fw ar v) (h : FIn G w env F K fw ar v args)
    (hx : Val w env xT x) (tx : Tm w L 1 xT env) (hxV : x < V) (hj : Val w env jT j)
    (tj : Tm w L 1 jT env) (hjd : j < degN G x) : Tm w L 1 (vbitT F xT jT) env := by
  have hL := t.hL
  have hp := h.hA.vport _ (Above.refl _) _ _ _ _ hx hj hxV hjd
  have tp := t.hT.tport _ (Ext.refl _) _ _ _ _ hx tx hj tj hxV hjd
  have hpM := portN_lt hxV hjd
  have htg := val_tgroupT h.hA h.vK hp hpM
  have ttg := tm_tgroupT h.hA t.hT h.vK t.tK t.hK1 hp tp hpM
  have := tgroupC_lt G t.hK1 (portN G x j)
  exact tm_bitT t h (val_add h.vK htg) (tm_add (d := 2) t.tK ttg le_rfl le_rfl (by norm_num)
      (by omega)) (by norm_num) (by omega)
    (val_hePosT h.hA h.vK h.vv htg hp hpM
      ((val_eqT (h.hA.vw _ (Above.refl _) _ _ hp hpM) hx).congr (ite_decide_toNat _)))
    (tm_hePosT h.hA t.hT h.vK t.tK t.hK1 t.tv ttg hp tp hpM
      (t_eqT' (t.hT.tw _ (Ext.refl _) _ _ hp tp hpM) tx (by omega)))

theorem val_argAT (h : FIn G w env F K fw ar v args) (hx : Val w env xT x) (hxV : x < V) :
    Val w env (argAT F xT) (argA G K ar fw v args x) :=
  val_sumT (g := fun j => (vbitC G K ar fw v args x j).toNat * 2 ^ j)
    (h.hA.vdeg _ (Above.refl _) _ _ hx hxV) fun pre y k hk =>
    val_mul (val_vbitT (h.up (above_at2 pre y k)) (hx.at2 pre y k) hxV (val_idx _ y k) hk)
      (val_pow2 (val_idx _ y k))

theorem argA_lt (x : ℕ) : argA G K ar fw v args x < 2 ^ degN G x :=
  sum_toNat_lt _ _

theorem degN_le (t : FTiers G w L env F K fw ar v) (hxV : x < V) : degN G x ≤ L := by
  rw [show x = ((⟨x, hxV⟩ : Fin V) : ℕ) from rfl, degN_fin]; exact t.hT.hΔ _

theorem tm_argAT (t : FTiers G w L env F K fw ar v) (h : FIn G w env F K fw ar v args)
    (hx : Val w env xT x) (tx : Tm w L 1 xT env) (hxV : x < V) : Tm w L 1 (argAT F xT) env := by
  have hL := t.hL
  have hd := degN_le t hxV
  refine tm_val (tm_sumTb (dn := 1) (db := 2) (h.hA.vdeg _ (Above.refl _) _ _ hx hxV)
    (t.hT.tdeg _ (Ext.refl _) _ _ hx tx hxV) (fun E hE y k hy hk ty => ?_) (by omega) (by norm_num))
    (val_argAT h hx hxV)
    ((argA_lt x).trans_le (by rw [one_mul]; exact Nat.pow_le_pow_right (by norm_num) hd))
  exact t_mul (tm_vbitT (t.up hE) (h.up (ext_above hE)) (hx.up (ext_above hE)) (tx.ext hE) hxV hy ty
    hk) (t_pow2 (d := 1) ty (by norm_num) (fun pre _ => by rw [(hy.ext pre).2]; omega) (by norm_num)
      (by omega)) (by norm_num)

theorem val_vfacT (h : FIn G w env F K fw ar v args) (hx : Val w env xT x) (hxV : x < V) :
    Val w env (vfacT F xT)
      (if vgroupC G K x = v then evalN G x (argA G K ar fw v args x) else 1) :=
  (val_ite (val_eqT (val_vgroupT h.hA h.vK hx) h.vv)
    (h.hA.veval _ (Above.refl _) _ _ _ _ hx (val_argAT h hx hxV) hxV (argA_lt x))
    (val_const 1)).congr (ite_ind _ _)

theorem tm_vfacT (t : FTiers G w L env F K fw ar v) (h : FIn G w env F K fw ar v args)
    (hx : Val w env xT x) (tx : Tm w L 1 xT env) (hxV : x < V) : Tm w L 1 (vfacT F xT) env := by
  have hL := t.hL
  exact tm_ite (t_eqT' (tm_vgroupT h.hA t.hT t.tK tx) t.tv (by omega))
    (t.hT.teval _ (Ext.refl _) _ _ _ _ hx tx (val_argAT h hx hxV) (tm_argAT t h hx tx hxV) hxV
      (argA_lt x)) (tcst (by norm_num) le_rfl hL)

/-! ### The test factors -/

/-- The end `b` of edge `e` (`false`: the `u` end). -/
def endT (N : NetT) (e : Term) : Bool → Term
  | false => N.uT e
  | true => N.wT e

/-- The bit of the half-edge `(e, b)` from the label of the vertex group of its end (`tbitC`). -/
def tbitT (F : FirstT) (e : Term) (b : Bool) : Term :=
  bitT F (vgroupT F.N F.KT (endT F.N e b))
    (hePosT F.N F.KT (vgroupT F.N F.KT (endT F.N e b)) (sub F.vT F.KT) e (const b.toNat))

/-- The factor of edge `e` (the equality test of its subdividing vertex) in the entry of test
group `v - K`. -/
def efacT (F : FirstT) (e : Term) : Term :=
  ite (eqT (tgroupT F.N F.KT e) (sub F.vT F.KT)) (eqT (tbitT F e false) (tbitT F e true)) (const 1)

variable {eT : Term} {e : ℕ}

theorem val_endT (h : FIn G w env F K fw ar v args) (he : Val w env eT e) (heM : e < G.M)
    (b : Bool) : Val w env (endT F.N eT b) (if b then wN G e else uN G e) := by
  cases b
  · exact h.hA.vu _ (Above.refl _) _ _ he heM
  · exact h.hA.vw _ (Above.refl _) _ _ he heM

theorem tm_endT (t : FTiers G w L env F K fw ar v) (he : Val w env eT e) (te : Tm w L 1 eT env)
    (heM : e < G.M) (b : Bool) : Tm w L 1 (endT F.N eT b) env := by
  cases b
  · exact t.hT.tu _ (Ext.refl _) _ _ he te heM
  · exact t.hT.tw _ (Ext.refl _) _ _ he te heM

theorem val_tbitT (h : FIn G w env F K fw ar v args) (he : Val w env eT e) (heM : e < G.M)
    (b : Bool) : Val w env (tbitT F eT b) (tbitC G K ar fw v args e b).toNat :=
  val_bitT h (val_vgroupT h.hA h.vK (val_endT h he heM b))
    (val_hePosT h.hA h.vK (val_vgroupT h.hA h.vK (val_endT h he heM b)) (val_sub h.vv h.vK) he heM
      (val_const _))

theorem tm_tbitT (t : FTiers G w L env F K fw ar v) (h : FIn G w env F K fw ar v args)
    (he : Val w env eT e) (te : Tm w L 1 eT env) (heM : e < G.M) (b : Bool) :
    Tm w L 1 (tbitT F eT b) env := by
  have hL := t.hL
  have hg := vgroupC_lt G t.hK1 (if b then wN G e else uN G e)
  have tg := tm_vgroupT h.hA t.hT t.tK (tm_endT t he te heM b)
  exact tm_bitT t h (val_vgroupT h.hA h.vK (val_endT h he heM b)) tg (by norm_num) (by omega)
    (val_hePosT h.hA h.vK (val_vgroupT h.hA h.vK (val_endT h he heM b)) (val_sub h.vv h.vK) he heM
      (val_const _))
    (tm_hePosT h.hA t.hT h.vK t.tK t.hK1 tg (t_sub t.tv t.tK) he te heM
      (t_small (Bool.toNat_le b |>.trans (by norm_num)) (by omega)))

theorem val_efacT (h : FIn G w env F K fw ar v args) (he : Val w env eT e) (heM : e < G.M) :
    Val w env (efacT F eT) (if tgroupC G K e = v - K then
      (if tbitC G K ar fw v args e false = tbitC G K ar fw v args e true then 1 else 0) else 1) :=
  (val_ite (val_eqT (val_tgroupT h.hA h.vK he heM) (val_sub h.vv h.vK))
    ((val_eqT (val_tbitT h he heM false) (val_tbitT h he heM true)).congr (ite_toNat_eq _ _))
    (val_const 1)).congr (ite_ind _ _)

theorem tm_efacT (t : FTiers G w L env F K fw ar v) (h : FIn G w env F K fw ar v args)
    (he : Val w env eT e) (te : Tm w L 1 eT env) (heM : e < G.M) : Tm w L 1 (efacT F eT) env := by
  have hL := t.hL
  exact tm_ite (t_eqT' (tm_tgroupT h.hA t.hT h.vK t.tK t.hK1 he te heM) (t_sub t.tv t.tK)
      (by omega))
    (t_eqT' (tm_tbitT t h he te heM false) (tm_tbitT t h he te heM true) (by omega))
    (tcst (by norm_num) le_rfl hL)

/-! ### The leaf factor -/

/-- **The leaf factor `f`** of the entry of node `v` of the first clique (`factor0C`). -/
def factor0T (F : FirstT) (fT : Term) : Term :=
  ite (eqT fT (const 0)) (enc0T F)
    (ite (lt F.vT F.KT)
      (ite (lt (sub fT (const 1)) F.N.VT) (vfacT F (sub fT (const 1))) (const 1))
      (ite (lt (sub fT (const 1)) F.N.MT) (efacT F (sub fT (const 1))) (const 1)))

variable {fT : Term} {f : ℕ}

theorem val_factor0T (h : FIn G w env F K fw ar v args) (hf : Val w env fT f) :
    Val w env (factor0T F fT) (factor0C G K ar fw v args f) := by
  have hx := val_sub hf (val_const 1)
  refine (val_ite (val_eqT hf (val_const 0)) (val_enc0T h)
    (val_ite (val_lt h.vv h.vK)
      (val_ite_cond (val_lt hx h.hA.vV)
          (fun hc => val_vfacT h hx (of_pos_ind hc)) fun _ => val_const 1)
      (val_ite_cond (val_lt hx h.hA.vM) (fun hc => val_efacT h hx (of_pos_ind hc))
        fun _ => val_const 1))).congr ?_
  simp only [ite_ind]
  rfl

theorem tm_factor0T (t : FTiers G w L env F K fw ar v) (h : FIn G w env F K fw ar v args)
    (hf : Val w env fT f) (tf : Tm w L 1 fT env) : Tm w L 1 (factor0T F fT) env := by
  have hL := t.hL
  have hx := val_sub hf (val_const 1)
  have tx : Tm w L 1 (sub fT (const 1)) env := t_sub tf (tcst (k := 1) (by norm_num) le_rfl hL)
  have cV := val_lt hx h.hA.vV
  have cM := val_lt hx h.hA.vM
  exact tm_ite (t_eqT' tf (tcst (by norm_num) le_rfl hL) (by omega)) (tm_enc0T t h)
    (tm_ite (t_lt t.tv t.tK (by omega))
      (tm_ite_cond (t_lt tx t.hT.tV (by omega)) cV.1
        (fun hc => tm_vfacT t h hx tx (of_pos_ind (cV.2 ▸ hc))) (tcst (by norm_num) le_rfl hL))
      (tm_ite_cond (t_lt tx t.hT.tM (by omega)) cM.1
        (fun hc => tm_efacT t h hx tx (of_pos_ind (cM.2 ▸ hc))) (tcst (by norm_num) le_rfl hL)))

/-- **The leaf factors of the first clique, as terms.** For a network with nonnegative vertex
functions, read through accessors with the value contract `NetAcc`, the budget array
`arrN (2K) fw (extN (firstBudget G K))` and budgets that fit in `fw` bits, `factor0T` denotes
`Setup.factor0 v args f` at every node `v < 2K` (it is a nonnegative integer). -/
theorem factor0T_eq (S : Setup) (hK : 1 ≤ S.K) (hC : Fits S.fw S.C₀.a) (hnn : EvalNonneg S.G)
    (hv : v < 2 * S.K)
    (h : FIn S.G w env F S.K S.fw (arrN (2 * S.K) S.fw (extN (firstBudget S.G S.K))) v args)
    (hf : Val w env fT f) :
    (((factor0T F fT).denote w env : ℕ) : ℤ) = S.factor0 v args f := by
  rw [(val_factor0T h hf).2]
  exact factor0C_eq S hK hC hnn hv args f

/-! ### The budget array -/

/-- Digit `t` of the budget array of the first clique (`firstDigit`). -/
def firstDigT (N : NetT) (KT qT t : Term) : Term :=
  ite (lt (div t qT) KT)
    (ite (lt (mod t qT) KT) (const 0)
      (div (mul (widthT N KT (div t qT) (sub (mod t qT) KT))
        (add (widthT N KT (div t qT) (sub (mod t qT) KT)) (const 1))) (const 2)))
    (const 0)

/-- **The budget array of the first clique**: `∑_t digit_t · 2^(t·fw)` over the `q·q` digits. -/
def firstArrT (N : NetT) (KT qT fwT : Term) : Term :=
  sumT (mul qT qT) fun t => mul (firstDigT N KT qT t) (pow2 (mul t fwT))

variable {qT tT : Term} {KT : Term} {N : NetT} {fwT : Term} {tv : ℕ}

theorem val_firstDigT (hA : NetAcc G w env N) (hK : Val w env KT K) (hq : Val w env qT (2 * K))
    (ht : Val w env tT tv) : Val w env (firstDigT N KT qT tT) (firstDigit G K tv) := by
  have hd := val_div ht hq
  have hm := val_mod ht hq
  have hW := val_widthT hA hK hd (val_sub hm hK)
  refine (val_ite (val_lt hd hK) (val_ite (val_lt hm hK) (val_const 0)
    (val_div (val_mul hW (val_add hW (val_const 1))) (val_const 2))) (val_const 0)).congr ?_
  rw [ite_ind, ite_ind, firstDigit]
  by_cases h1 : tv / (2 * K) < K
  · by_cases h2 : tv % (2 * K) < K
    · rw [ite_eq_left h1, ite_eq_left h2, ite_eq_right (by omega)]
    · rw [ite_eq_left h1, ite_eq_right h2, ite_eq_left ⟨h1, by omega⟩]
  · rw [ite_eq_right h1, ite_eq_right (by omega)]

theorem tm_firstDigT (hA : NetAcc G w env N) (hT : NetTiers G w L env N) (hK : Val w env KT K)
    (tK : Tm w L 1 KT env) (hK1 : 1 ≤ K) (tq : Tm w L 1 qT env) {dt : ℕ} (tt : Tm w L dt tT env) :
        Tm w L 7 (firstDigT N KT qT tT) env := by
  have hL := hT.hL
  have tW := tm_widthT hA hT hK tK hK1 (t_div tt tq) (t_sub (t_mod_left tt tq) tK)
  exact tm_ite (t_lt (t_div tt tq) tK (by omega))
    (tm_ite (t_lt (t_mod_left tt tq) tK (by omega)) (tcst (by norm_num) (by norm_num) hL)
      (t_div (tm_mul tW (tm_add (d := 4) tW (tcst (k := 1) (by norm_num) le_rfl hL) le_rfl
        (by norm_num) (by norm_num) (by omega)) (by norm_num) (by norm_num))
        (tcst (k := 2) (by norm_num) le_rfl hL)))
    (tcst (by norm_num) (by norm_num) hL)

theorem sum_digits_eq (fw n : ℕ) (d : ℕ → ℕ) :
    ∑ k ∈ range n, d k * 2 ^ (k * fw) = packN fw n d := by
  unfold packN
  refine sum_congr rfl fun k _ => ?_
  rw [← pow_mul, mul_comm fw k, mul_comm]

theorem val_firstArrT (hA : NetAcc G w env N) (hK : Val w env KT K) (hq : Val w env qT (2 * K))
    (hfw : Val w env fwT fw) :
    Val w env (firstArrT N KT qT fwT) (arrN (2 * K) fw (extN (firstBudget G K))) := by
  rw [arrN_firstBudget, ← sum_digits_eq]
  exact val_sumT (g := fun t => firstDigit G K t * 2 ^ (t * fw)) (val_mul hq hq) fun pre x k _ =>
    val_mul (val_firstDigT (hA.up (above_at2 pre x k)) (hK.at2 pre x k) (hq.at2 pre x k)
      (val_idx _ x k)) (val_pow2 (val_mul (val_idx _ x k) (hfw.at2 pre x k)))

/-- **The tier of the budget array**: `d` when the `4K²` digits of `fw` bits fit in `d·L` bits. -/
theorem tm_firstArrT {d : ℕ} (hA : NetAcc G w env N) (hT : NetTiers G w L env N)
    (hK : Val w env KT K) (tK : Tm w L 1 KT env) (hK1 : 1 ≤ K) (hq : Val w env qT (2 * K))
    (tq : Tm w L 1 qT env) (hfw : Val w env fwT fw) (tfw : Tm w L 1 fwT env) (hfwL : fw < L)
    (hC : Fits fw (firstBudget G K)) (hd : 2 * K * (2 * K) * fw ≤ d * L) (hd1 : 1 ≤ d)
    (hd32 : d ≤ 32) : Tm w L d (firstArrT N KT qT fwT) env := by
  have hL := hT.hL
  have hdig : ∀ {E : List ℕ} {t : Term} {k : ℕ}, Above env E → Val w E t k →
      Val w E (mul (firstDigT N KT qT t) (pow2 (mul t fwT))) (firstDigit G K k * 2 ^ (k * fw)) :=
    fun hE ht => val_mul (val_firstDigT (hA.up hE) (hK.up hE) (hq.up hE) ht)
      (val_pow2 (val_mul ht (hfw.up hE)))
  change Tm w L d (foldT (mul qT qT) (const 0) fun acc t =>
    add acc (mul (firstDigT N KT qT t) (pow2 (mul t fwT)))) env
  refine tm_foldT_st (N := 2 * K * (2 * K)) (val_mul hq hq) (t_mul tq tq (by norm_num))
    (by norm_num) (tcst (k := 0) (by norm_num) le_rfl hL) hd32 (fun pre _ k hk => ?_)
    (fun pre x k _ hk hx hE => ?_)
  · have hs := val_sumT (env := pre ++ env) (n := const k)
      (body := fun t => mul (firstDigT N KT qT t) (pow2 (mul t fwT)))
      (g := fun t => firstDigit G K t * 2 ^ (t * fw)) (val_const k)
      fun pre' x' k' _ => hdig ⟨x' :: k' :: (pre' ++ pre), by simp⟩ (val_idx _ x' k')
    refine lt_of_eq_of_lt hs.2 ?_
    rw [sum_digits_eq]
    calc packN fw k (firstDigit G K) < 2 ^ (k * fw) :=
          packN_lt fun t ht => firstDigit_lt G K hC (by omega)
      _ ≤ 2 ^ (d * L) := Nat.pow_le_pow_right (by norm_num)
          ((Nat.mul_le_mul_right _ hk).trans hd)
  · have hE' := ext_above hE
    have hkv := val_idx (w := w) (pre ++ env) x k
    have hN := (t_mul tq tq (by norm_num : 1 + 1 ≤ 128)).lt
    rw [(val_mul hq hq).2] at hN
    have tk : Tm w L (1 + 1) (lvl (pre ++ env).length) (x :: k :: (pre ++ env)) :=
      tm_idx (hk.trans hN)
    have tdig : Tm w L 1 (firstDigT N KT qT (lvl (pre ++ env).length)) (x :: k :: (pre ++ env)) :=
      tm_val (tm_firstDigT (hA.up hE') (hT.up hE) (hK.up hE') (tK.ext hE) hK1
        (tq.ext hE) tk) (val_firstDigT (hA.up hE') (hK.up hE') (hq.up hE') hkv)
        (lt_of_lt_of_le (firstDigit_lt G K hC hk)
          (by rw [one_mul]; exact Nat.pow_le_pow_right (by norm_num) hfwL.le))
    have he := val_mul hkv (hfw.up hE')
    have hexp : k * fw < d * L := by
      rcases Nat.eq_zero_or_pos fw with h0 | h0
      · rw [h0, Nat.mul_zero]; exact Nat.mul_pos (by omega) (by omega)
      · have := Nat.mul_lt_mul_of_pos_right hk h0; omega
    have tp : Tm w L d (pow2 (mul (lvl (pre ++ env).length) fwT)) (x :: k :: (pre ++ env)) :=
      t_pow2_stable (t_mul tk (tfw.ext hE) (by norm_num)) (by norm_num) he.1
        (by rw [he.2]; exact hexp) hd32 (by omega)
    exact (tm_add (d := d + 2) (tm_acc hx) (tm_mul (d := d + 1) tdig tp (by omega) (by omega))
      (by omega) (by omega) (by omega) (by omega)).mono (by omega)

end Cslib.Complexity.NtimeDspace.Cube.Num
