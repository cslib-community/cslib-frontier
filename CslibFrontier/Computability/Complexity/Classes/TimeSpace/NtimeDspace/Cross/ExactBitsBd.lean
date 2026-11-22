/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.ExactBits

/-!
# Value bounds of the residue-to-binary program

Every value arising in the program of `ExactBits` is at most `M`, under the size conditions
`Sizes`: the width `W ≥ 2` with `X^r < 2^W` and `X + 1 ≤ 2^(W-1)`, `E / r < g`, `E + 1 ≤ M`,
and `4 (X + 1) 2^W (W^g + 1) ≤ M`. The residue program is called only at selected primes, where
it is assumed bounded and correct (`ResOK`).
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Cross.Exact

open NtimeDspace.ProgLang NtimeDspace.ProgTerm Term NtimeDspace.SumProduct Finset

variable {w : List Bool} {env : List ℕ} {M : ℕ}

/-- The size conditions. -/
structure Sizes (s : SC) (M : ℕ) : Prop where
  hW : 2 ≤ s.W
  hr : 1 ≤ s.r
  hXr : s.X ^ s.r < 2 ^ s.W
  hK : s.X + 1 ≤ 2 ^ (s.W - 1)
  hg : s.E / s.r < s.g
  hE : s.E + 1 ≤ M
  hM : 4 * ((s.X + 1) * 2 ^ s.W * (s.W ^ s.g + 1)) ≤ M

/-- The residue program is bounded by `M` and gives residues below `p` at the selected primes. -/
def ResOK (w : List Bool) (q : Prog) (s : SC) (M : ℕ) : Prop :=
  ∀ p, sel s.H s.X s.E p → q.Bounded w M [s.τ, s.n, p] ∧ resOf w q s p < p

variable (w M) in
/-- The parameter terms are bounded (they are variables in the program). -/
def Ctx.GoodB (c : Ctx) (env : List ℕ) : Prop :=
  Bd w M c.τ env ∧ Bd w M c.n env ∧ Bd w M c.H env ∧ Bd w M c.X env ∧ Bd w M c.E env ∧
    Bd w M c.W env ∧ Bd w M c.r env ∧ Bd w M c.g env ∧ Bd w M c.Wg env

theorem Ctx.GoodB.ext {c : Ctx} (h : c.GoodB w M env) (pre : List ℕ) : c.GoodB w M (pre ++ env) :=
  ⟨h.1.ext pre, h.2.1.ext pre, h.2.2.1.ext pre, h.2.2.2.1.ext pre, h.2.2.2.2.1.ext pre,
    h.2.2.2.2.2.1.ext pre, h.2.2.2.2.2.2.1.ext pre, h.2.2.2.2.2.2.2.1.ext pre,
    h.2.2.2.2.2.2.2.2.ext pre⟩

variable {c : Ctx} {s : SC} {q : Prog}

namespace Sizes

variable (hs : Sizes s M)
include hs

theorem X1_le_two_pow : s.X + 1 ≤ 2 ^ s.W :=
  hs.hK.trans (Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _))

theorem one_le_Wg : 1 ≤ s.W ^ s.g := Nat.one_le_pow _ _ (by have := hs.hW; omega)

theorem base_le : (s.X + 1) * 2 ^ s.W * (s.W ^ s.g + 1) ≤ M := by have := hs.hM; omega

theorem two_pow_le : 2 ^ s.W ≤ M := by
  have h := hs.base_le
  have h1 : 1 ≤ s.X + 1 := by omega
  have h2 : 1 ≤ s.W ^ s.g + 1 := by omega
  calc 2 ^ s.W = 1 * 2 ^ s.W * 1 := by ring
    _ ≤ (s.X + 1) * 2 ^ s.W * (s.W ^ s.g + 1) := by gcongr
    _ ≤ M := h

theorem four_le : 4 ≤ M := by
  have := hs.two_pow_le
  have : 4 ≤ 2 ^ s.W := by
    calc 4 = 2 ^ 2 := rfl
      _ ≤ 2 ^ s.W := Nat.pow_le_pow_right (by norm_num) hs.hW
  omega

theorem X1_le : s.X + 1 ≤ M := (hs.X1_le_two_pow).trans hs.two_pow_le

theorem X1_sq_le : (s.X + 1) * (s.X + 1) ≤ M := by
  calc (s.X + 1) * (s.X + 1) ≤ (s.X + 1) * 2 ^ s.W * 1 := by
        rw [mul_one]; exact Nat.mul_le_mul_left _ hs.X1_le_two_pow
    _ ≤ (s.X + 1) * 2 ^ s.W * (s.W ^ s.g + 1) := Nat.mul_le_mul_left _ (by omega)
    _ ≤ M := hs.base_le

theorem Wg_le : s.W ^ s.g ≤ M := by
  calc s.W ^ s.g ≤ 1 * 1 * (s.W ^ s.g + 1) := by omega
    _ ≤ (s.X + 1) * 2 ^ s.W * (s.W ^ s.g + 1) := by
        gcongr
        · omega
        · exact Nat.one_le_two_pow
    _ ≤ M := hs.base_le

theorem col_le : (s.X + 1) * s.W ^ s.g ≤ M := by
  calc (s.X + 1) * s.W ^ s.g ≤ (s.X + 1) * 1 * (s.W ^ s.g + 1) := by
        rw [mul_one]; exact Nat.mul_le_mul_left _ (by omega)
    _ ≤ (s.X + 1) * 2 ^ s.W * (s.W ^ s.g + 1) := by gcongr; exact Nat.one_le_two_pow
    _ ≤ M := hs.base_le

theorem two_col_le : 2 * ((s.X + 1) * s.W ^ s.g + 2) ≤ M := by
  have h := hs.hM
  have h2 : 4 ≤ 2 ^ s.W := by
    calc 4 = 2 ^ 2 := rfl
      _ ≤ 2 ^ s.W := Nat.pow_le_pow_right (by norm_num) hs.hW
  have : (s.X + 1) * 4 * (s.W ^ s.g + 1) ≤ (s.X + 1) * 2 ^ s.W * (s.W ^ s.g + 1) := by gcongr
  have e : (s.X + 1) * 4 * (s.W ^ s.g + 1) = 4 * ((s.X + 1) * s.W ^ s.g) + 4 * (s.X + 1) := by ring
  omega

theorem gW_le : (s.g + 1) * s.W ≤ M := by
  have hg : s.g + 1 ≤ s.W ^ s.g + 1 := by
    have : s.g < 2 ^ s.g := Nat.lt_two_pow_self
    have : 2 ^ s.g ≤ s.W ^ s.g := Nat.pow_le_pow_left hs.hW _
    omega
  have hW : s.W ≤ 2 ^ s.W := Nat.lt_two_pow_self.le
  calc (s.g + 1) * s.W ≤ (s.W ^ s.g + 1) * 2 ^ s.W := Nat.mul_le_mul hg hW
    _ = 1 * 2 ^ s.W * (s.W ^ s.g + 1) := by ring
    _ ≤ (s.X + 1) * 2 ^ s.W * (s.W ^ s.g + 1) := by gcongr; omega
    _ ≤ M := hs.base_le

theorem g_le : s.g ≤ M := by have := hs.gW_le; have := hs.hW; nlinarith

theorem gW'_le : s.g * s.W ≤ M := le_trans (Nat.mul_le_mul_right _ (Nat.le_succ _)) hs.gW_le

theorem kq_le_bound : (s.X + 1) * 2 ^ s.W + (s.X + 1) ≤ M := by
  have h := hs.base_le
  have : (s.X + 1) * 2 ^ s.W * 2 ≤ (s.X + 1) * 2 ^ s.W * (s.W ^ s.g + 1) :=
    Nat.mul_le_mul_left _ (by have := hs.one_le_Wg; omega)
  have : s.X + 1 ≤ (s.X + 1) * 2 ^ s.W := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
  omega

end Sizes

/-! ### Bounds of the pieces -/

theorem bd_primeT {x : Term} {v : ℕ} (hx : Val w x env v) (hbx : Bd w M x env) (hv : v ≤ M)
    (h2 : 2 ≤ M) : Bd w M (primeT x) env := by
  have hb : FVal w (fun d => lt (const 0) (mod x (add d (const 2)))) env
      (fun d => if 0 < v % (d + 2) then 1 else 0) := fun pre u p hu =>
    val_lt (val_const 0 _) (val_mod (hx.ext pre) (val_add hu (val_const 2 _)))
  have hp := val_prodT (val_sub hx (val_const 2 env)) hb
  refine bd_mul (bd_lt (bd_const (by omega) _) hbx) ?_ (val_lt (val_const 1 env) hx) hp ?_
  · refine bd_prodT (val_sub hx (val_const 2 env)) hb (bd_sub hbx (bd_const h2 _)) (by omega)
      (by omega) (fun k _ => ?_) fun pre u q hq hu hbu => ?_
    · exact (prod_le_one fun i _ => by split_ifs <;> omega).trans (by omega)
    · exact bd_lt (bd_const (Nat.zero_le _) _) (bd_mod (hbx.ext pre)
        (bd_add hbu (bd_const h2 _) hu (val_const 2 _) (by omega)))
  · have : (∏ k ∈ range (v - 2), if 0 < v % (k + 2) then 1 else 0) ≤ 1 :=
      prod_le_one fun i _ => by split_ifs <;> omega
    calc (if 1 < v then 1 else 0) * ∏ k ∈ range (v - 2), (if 0 < v % (k + 2) then 1 else 0)
        ≤ 1 * 1 := Nat.mul_le_mul (by split_ifs <;> omega) this
      _ ≤ M := by omega

theorem bd_candT (hc : c.Good w s env) (hcb : c.GoodB w M env) (hs : Sizes s M) {x : Term}
    {v : ℕ} (hx : Val w x env v) (hbx : Bd w M x env) (hv : v ≤ M) : Bd w M (candT c x) env := by
  have hm := hs.four_le
  refine bd_mul (bd_mul (bd_lt hcb.2.2.1 hbx) (bd_lt hbx (bd_add hcb.2.2.2.1 (bd_const (by omega) _)
    hc.2.2.2.1 (val_const 1 _) hs.X1_le)) (val_lt hc.2.2.1 hx)
    (val_lt hx (val_add hc.2.2.2.1 (val_const 1 env))) (by split_ifs <;> omega))
    (bd_primeT hx hbx hv (by omega)) (val_mul (val_lt hc.2.2.1 hx)
      (val_lt hx (val_add hc.2.2.2.1 (val_const 1 env)))) (val_primeT hx) ?_
  split_ifs <;> omega

theorem bd_rankT (hc : c.Good w s env) (hcb : c.GoodB w M env) (hs : Sizes s M) {x : Term}
    {v : ℕ} (hx : Val w x env v) (hbx : Bd w M x env) (hv : v ≤ M) : Bd w M (rankT c x) env := by
  refine bd_sumT hx (fun pre u p hu => val_candT (hc.ext pre) hu) hbx hv ?_
    fun pre u k hk hu hbu => bd_candT (hc.ext pre) (hcb.ext pre) hs hu hbu (by omega)
  calc ∑ k ∈ range v, (if cand s.H s.X k then 1 else 0) ≤ ∑ _k ∈ range v, 1 :=
        sum_le_sum fun k _ => by split_ifs <;> omega
    _ ≤ M := by simp [hv]

theorem rank_le (H X v : ℕ) : rank H X v ≤ v := by
  rw [rank]; exact Nat.count_le _

theorem bd_selT (hc : c.Good w s env) (hcb : c.GoodB w M env) (hs : Sizes s M) {x : Term}
    {v : ℕ} (hx : Val w x env v) (hbx : Bd w M x env) (hv : v ≤ M) : Bd w M (selT c x) env := by
  have hm := hs.four_le
  refine bd_mul (bd_candT hc hcb hs hx hbx hv) (bd_lt (bd_rankT hc hcb hs hx hbx hv)
    (bd_add hcb.2.2.2.2.1 (bd_const (by omega) _) hc.2.2.2.2.1 (val_const 1 _) hs.hE))
    (val_candT hc hx) (val_lt (val_rankT hc hx) (val_add hc.2.2.2.2.1 (val_const 1 env))) ?_
  split_ifs <;> omega

theorem bd_grpT (hc : c.Good w s env) (hcb : c.GoodB w M env) (hs : Sizes s M) {x : Term}
    {v : ℕ} (hx : Val w x env v) (hbx : Bd w M x env) (hv : v ≤ M) : Bd w M (grpT c x) env :=
  bd_div (bd_rankT hc hcb hs hx hbx hv) hcb.2.2.2.2.2.2.1

theorem grp_le (H X r v : ℕ) : grp H X r v ≤ v := (Nat.div_le_self _ _).trans (rank_le H X v)

theorem Qm_pos (H X E r m : ℕ) : 1 ≤ Qm H X E r m := by
  unfold Qm
  refine Finset.one_le_prod' fun x _ => ?_
  split_ifs with h
  · exact (sel_prime h.1).one_lt.le
  · exact le_rfl

theorem bd_QmT (hc : c.Good w s env) (hcb : c.GoodB w M env) (hs : Sizes s M) {m : Term}
    {v : ℕ} (hm : Val w m env v) (hbm : Bd w M m env) (hv : v ≤ M) : Bd w M (QmT c m) env := by
  have h4 := hs.four_le
  have hb : FVal w (fun x => ite (mul (selT c x) (eqT (grpT c x) m)) x (const 1)) env
      (fun x => if sel s.H s.X s.E x ∧ grp s.H s.X s.r x = v then x else 1) := by
    intro pre u p hu
    have := val_ite (val_mul (val_selT (hc.ext pre) hu) (val_eqT (val_grpT (hc.ext pre) hu)
      (hm.ext pre))) hu (val_const 1 _)
    refine fun extra => (this extra).trans ?_
    by_cases h1 : sel s.H s.X s.E p <;> by_cases h2 : grp s.H s.X s.r p = v <;> simp [h1, h2]
  refine bd_prodT (val_add hc.2.2.2.1 (val_const 1 env)) hb
    (bd_add hcb.2.2.2.1 (bd_const (by omega) _) hc.2.2.2.1 (val_const 1 _) hs.X1_le) hs.X1_le
    (by omega) (fun k hk => ?_) fun pre u p hp hu hbu => ?_
  · refine le_trans ?_ ((Qm_lt (H := s.H) (E := s.E) (by have := hs.hW; omega) hs.hr hs.hXr
      v).le.trans hs.two_pow_le)
    unfold Qm
    exact prod_le_prod_of_subset_of_one_le (range_subset_range.mpr (by omega))
      fun x _ _ => by split_ifs with h; exacts [(sel_prime h.1).one_lt.le, le_rfl]
  · have hc' := hc.ext pre
    have hcb' := hcb.ext pre
    have hpM : p ≤ M := by have := hs.X1_le; omega
    refine bd_ite (bd_mul (bd_selT hc' hcb' hs hu hbu hpM) (bd_eqT (bd_grpT hc' hcb' hs hu hbu hpM)
      (hbm.ext pre) (val_grpT hc' hu) (hm.ext pre) ((grp_le _ _ _ _).trans hpM) hv (by omega))
      (val_selT hc' hu) (val_eqT (val_grpT hc' hu) (hm.ext pre)) (by split_ifs <;> omega))
      (val_mul (val_selT hc' hu) (val_eqT (val_grpT hc' hu) (hm.ext pre))) (fun _ => hbu)
      fun _ => bd_const (by omega) _

theorem bd_invT (hc : c.Good w s env) (hcb : c.GoodB w M env) (hs : Sizes s M) {p : Term}
    {v : ℕ} (hp : Val w p env v) (hbp : Bd w M p env) (hv : 2 ≤ v) (hvX : v ≤ s.X) :
    Bd w M (invT c p) env := by
  have h4 := hs.four_le
  have hsq := hs.X1_sq_le
  have hb : FVal w (fun x => ite (mul (selT c x) (sub (const 1) (eqT x p))) x (const 1)) env
      (fun x => if sel s.H s.X s.E x ∧ x ≠ v then x else 1) := by
    intro pre u y hu
    have := val_ite (val_mul (val_selT (hc.ext pre) hu)
      (val_sub (val_const 1 _) (val_eqT hu (hp.ext pre)))) hu (val_const 1 _)
    refine fun extra => (this extra).trans ?_
    by_cases h1 : sel s.H s.X s.E y <;> by_cases h2 : y = v <;> simp [h1, h2]
  have hPB : v * (s.X + 1) ≤ M := le_trans (Nat.mul_le_mul_right _ (by omega)) hsq
  refine bd_letT (val_prodModT hp hv (val_add hc.2.2.2.1 (val_const 1 env)) hb) ?_ ?_
  · refine bd_prodModT hp hv (val_add hc.2.2.2.1 (val_const 1 env)) hb hbp
      (bd_add hcb.2.2.2.1 (bd_const (by omega) _) hc.2.2.2.1 (val_const 1 _) hs.X1_le) hs.X1_le
      (by omega) (B := s.X + 1) (fun k hk => by split_ifs <;> omega) hPB
      fun pre u y hy hu hbu => ?_
    have hc' := hc.ext pre
    have hcb' := hcb.ext pre
    have hyM : y ≤ M := by have := hs.X1_le; omega
    refine bd_ite (bd_mul (bd_selT hc' hcb' hs hu hbu hyM) (bd_sub (bd_const (by omega) _)
      (bd_eqT hbu (hbp.ext pre) hu (hp.ext pre) hyM (by have := hs.X1_le; omega) (by omega)))
      (val_selT hc' hu) (val_sub (val_const 1 _) (val_eqT hu (hp.ext pre)))
      (by split_ifs <;> omega))
      (val_mul (val_selT hc' hu) (val_sub (val_const 1 _) (val_eqT hu (hp.ext pre))))
      (fun _ => hbu) fun _ => bd_const (by omega) _
  · intro pre u hu hbu
    refine bd_prodModT (hp.ext pre) hv (val_sub (hp.ext pre) (val_const 2 _))
      (F := fun _ => (∏ x ∈ range (s.X + 1), if sel s.H s.X s.E x ∧ x ≠ v then x else 1) % v)
      (B := v) (fun pre' u' y _ => hu.ext pre') (hbp.ext pre)
      (bd_sub (hbp.ext pre) (bd_const (by omega) _)) (by have := hs.X1_le; omega) (by omega)
      (fun k _ => (Nat.mod_lt _ (by omega)).le)
      (le_trans (Nat.mul_le_mul (by omega) (by omega)) hsq) fun pre' u' y _ _ _ => hbu.ext pre'

theorem bd_bT (hq : Prog'.closed 3 q = true) (hc : c.Good w s env) (hcb : c.GoodB w M env)
    (hs : Sizes s M) (hR : ResOK w q s M) {p : Term} {v : ℕ} (hp : Val w p env v)
    (hbp : Bd w M p env) (hsel : sel s.H s.X s.E v) : Bd w M (bT q c p) env := by
  have hv := (sel_prime hsel).two_le
  have hvX := sel_le hsel
  obtain ⟨hRb, hRlt⟩ := hR v hsel
  refine bd_mod (bd_mul (bd_call3 hq hc.1 hc.2.1 hp hcb.1 hcb.2.1 hbp hRb)
    (bd_invT hc hcb hs hp hbp hv hvX) (val_call3 hq hc.1 hc.2.1 hp) (val_invT hc hp hv) ?_) hbp
  have hinv : invc s.H s.X s.E v < v := Nat.mod_lt _ (by omega)
  calc q.eval w [s.τ, s.n, v] * invc s.H s.X s.E v ≤ v * v := Nat.mul_le_mul hRlt.le hinv.le
    _ ≤ (s.X + 1) * (s.X + 1) := Nat.mul_le_mul (by omega) (by omega)
    _ ≤ M := hs.X1_sq_le

theorem bd_facT (hq : Prog'.closed 3 q = true) (hc : c.Good w s env) (hcb : c.GoodB w M env)
    (hs : Sizes s M) (hR : ResOK w q s M) {p m : Term} {v k : ℕ} (hp : Val w p env v)
    (hbp : Bd w M p env) (hsel : sel s.H s.X s.E v) (hm : Val w m env k) (hbm : Bd w M m env)
    (hk : k ≤ M) : Bd w M (facT q c p m) env := by
  have hv := (sel_prime hsel).two_le
  have hvM : v ≤ M := by have := sel_le hsel; have := hs.X1_le; omega
  have h4 := hs.four_le
  refine bd_ite (bd_eqT hbm (bd_grpT hc hcb hs hp hbp hvM) hm (val_grpT hc hp) hk
    ((grp_le _ _ _ _).trans hvM) (by omega)) (val_eqT hm (val_grpT hc hp)) (fun hpos => ?_)
    fun _ => bd_QmT hc hcb hs hm hbm hk
  have hkg : k = grp s.H s.X s.r v := by by_contra h; simp [h] at hpos
  refine bd_mul (bd_bT hq hc hcb hs hR hp hbp hsel) (bd_div (bd_QmT hc hcb hs hm hbm hk) hbp)
    (val_bT hq hc hp hv) (val_div (val_QmT hc hm) hp) ?_
  have hsS : v ∈ selSet s.H s.X s.E := mem_selSet.mpr ⟨sel_le hsel, hsel⟩
  subst hkg
  have := fac_lt (res := resOf w q s) (by have := hs.hW; omega) hs.hr hs.hXr hsS
    (grp s.H s.X s.r v)
  simp only [fac, if_true] at this
  exact this.le.trans hs.two_pow_le

theorem bd_pwT {x e : Term} {a b k : ℕ} (hx : Val w x env a) (he : Val w e env b)
    (hbx : Bd w M x env) (hbe : Bd w M e env) (hb : b ≤ k) (hk : a ^ k ≤ M) (ha : 1 ≤ a)
    (hbM : b ≤ M) : Bd w M (pwT x e) env := by
  have h1 : 1 ≤ M := (Nat.one_le_pow _ _ ha).trans hk
  refine bd_prodT he (F := fun _ => a) (fun pre _ _ _ => hx.ext pre) hbe hbM h1
    (fun j hj => ?_) fun pre _ _ _ _ _ => hbx.ext pre
  rw [prod_const, card_range]
  exact (Nat.pow_le_pow_right ha (by omega)).trans hk

theorem bd_digT (hc : c.Good w s env) (hcb : c.GoodB w M env) (hs : Sizes s M) {u m : Term}
    {a b : ℕ} (hu : Val w u env a) (hm : Val w m env b) (hbu : Bd w M u env) (hbm : Bd w M m env)
    (hb : b ≤ s.g) : Bd w M (digT c u m) env :=
  bd_mod (bd_div hbu (bd_pwT hc.2.2.2.2.2.1 hm hcb.2.2.2.2.2.1 hbm hb hs.Wg_le
    (by have := hs.hW; omega) (hb.trans hs.g_le))) hcb.2.2.2.2.2.1

theorem dig_le {W : ℕ} (hW : 1 ≤ W) (u m : ℕ) : dig W u m ≤ W := (Nat.mod_lt _ (by omega)).le

theorem bd_sdigT (hc : c.Good w s env) (hcb : c.GoodB w M env) (hs : Sizes s M) {u : Term}
    {a : ℕ} (hu : Val w u env a) (hbu : Bd w M u env) : Bd w M (sdigT c u) env := by
  refine bd_sumT hc.2.2.2.2.2.2.2.1 (fun pre m b hm => val_digT (hc.ext pre) (hu.ext pre) hm)
    hcb.2.2.2.2.2.2.2.1 hs.g_le ?_ fun pre m b hb hm hbm =>
      bd_digT (hc.ext pre) (hcb.ext pre) hs (hu.ext pre) hm (hbu.ext pre) hbm hb.le
  calc ∑ k ∈ range s.g, dig s.W a k ≤ ∑ _k ∈ range s.g, s.W :=
        sum_le_sum fun k _ => dig_le (by have := hs.hW; omega) a k
    _ = s.g * s.W := by simp
    _ ≤ M := hs.gW'_le

theorem sdig_le {W g : ℕ} (hW : 1 ≤ W) (u : ℕ) : sdig W g u ≤ g * W := by
  unfold sdig
  calc ∑ k ∈ range g, dig W u k ≤ ∑ _k ∈ range g, W := sum_le_sum fun k _ => dig_le hW u k
    _ = g * W := by simp

theorem bd_pbitsT (hc : c.Good w s env) (hcb : c.GoodB w M env) (hs : Sizes s M)
    {f : Term → Term} {F : ℕ → ℕ} (hf : FVal w f env F)
    (hbf : ∀ pre u k, k < s.g → Val w u (pre ++ env) k → Bd w M u (pre ++ env) →
      Bd w M (f u) (pre ++ env))
    {u : Term} {a : ℕ} (hu : Val w u env a) (hbu : Bd w M u env) :
    Bd w M (pbitsT c f u) env := by
  have h4 := hs.four_le
  refine bd_prodT hc.2.2.2.2.2.2.2.1 (fun pre m b hm => val_bit (hf pre m b hm)
    (val_digT (hc.ext pre) (hu.ext pre) hm)) hcb.2.2.2.2.2.2.2.1 hs.g_le (by omega)
    (fun k _ => (prod_le_one fun i _ => by omega).trans (by omega))
    fun pre m b hb hm hbm => bd_bit (hbf pre m b hb hm hbm)
      (bd_digT (hc.ext pre) (hcb.ext pre) hs (hu.ext pre) hm (hbu.ext pre) hbm hb.le)

end Cslib.Complexity.NtimeDspace.Cross.Exact
