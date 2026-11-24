/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.TameLib

/-!
# Folds whose counter value matters

Some bodies use the loop counter as an exponent, so its tier is not enough:
they need `i < V`. `tm_foldT_inv'` passes that bound to the body, and
`t_sumTv` is the corresponding sum. `t_powT_lt` bounds `x ^ i` for `i < V`.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.ProgTerm

open Term

variable {w : List Bool} {L : ℕ} {d d1 d2 da db dn : ℕ} {a b n e i x : Term} {env : List ℕ}

variable (w L) in
/-- The value of `t` is below `V` in every small extension. -/
def Sm (t : Term) (V : ℕ) (env : List ℕ) : Prop := ∀ pre, Small L pre → t.denote w (pre ++ env) < V

theorem Sm.ext {t : Term} {V : ℕ} (h : Sm w L t V env) {env' : List ℕ} (he : Ext L env' env) :
    Sm w L t V env' := by
  obtain ⟨p, hp, rfl⟩ := he
  exact fun pre hpre => by rw [← List.append_assoc]; exact h _ (hpre.append hp)

theorem Sm.of_stable {t : Term} {V : ℕ} (hs : StableAt w t env) (hv : t.denote w env < V) :
    Sm w L t V env := fun pre _ => by rw [hs pre]; exact hv

theorem StableAt.extend' {t : Term} (hs : StableAt w t env) {env' : List ℕ} (he : Ext L env' env) :
    StableAt w t env' := by
  obtain ⟨p, _, rfl⟩ := he; exact hs.extend p

theorem StableAt.extend'_eq {t : Term} (hs : StableAt w t env) {env' : List ℕ}
    (he : Ext L env' env) :
    t.denote w env' = t.denote w env := by
  obtain ⟨p, _, rfl⟩ := he; exact hs p

/-- A fold whose body may use a bound `V` on the counter. -/
theorem tm_foldT_inv' {init : Term} {f : Term → Term → Term} {di V : ℕ}
    (hn : Tm w L dn n env) (hdn : dn ≤ 32) (hnV : ∀ pre, Small L pre → n.denote w (pre ++ env) ≤ V)
    (hi : Tm w L di init env)
    (hf : ∀ env', Ext L env' env → ∀ x y, Tm w L da x env' → Tm w L dn y env' →
      StableAt w y env' → Sm w L y V env' → Tm w L db (f x y) env') (hda : da ≤ 32)
    (inv : ∀ pre, Small L pre → ∀ k ≤ n.denote w (pre ++ env),
      foldAcc w f (pre ++ env) (init.denote w (pre ++ env)) k < 2 ^ (da * L)) :
    Tm w L da (foldT n init f) env := fun pre hp => by
  obtain ⟨bn, vn⟩ := hn pre hp
  refine ⟨⟨bn, (hi pre hp).1, vn.le.trans (pow_le_pow_tier (by omega)), fun k hk => ?_⟩, ?_⟩
  · have hacc := inv pre hp k hk.le
    have hsm : Small L (foldAcc w f (pre ++ env) (init.denote w (pre ++ env)) k :: k :: pre) :=
      Small.cons (hacc.trans_le (pow_le_pow_tier hda))
        (Small.cons ((hk.trans vn).trans_le (pow_le_pow_tier hdn)) hp)
    have hx : Tm w L da (lvl ((pre ++ env).length + 1))
        ((foldAcc w f (pre ++ env) (init.denote w (pre ++ env)) k :: k :: pre) ++ env) := by
      simp only [List.cons_append]
      exact tm_lvl (by simp) (by simp [denote_lvl, hacc])
    have hy : Tm w L dn (lvl (pre ++ env).length)
        ((foldAcc w f (pre ++ env) (init.denote w (pre ++ env)) k :: k :: pre) ++ env) := by
      simp only [List.cons_append]
      exact tm_second (hk.trans vn)
    have hyv : Sm w L (lvl (pre ++ env).length) V
        ((foldAcc w f (pre ++ env) (init.denote w (pre ++ env)) k :: k :: pre) ++ env) := by
      intro pre' _
      simp only [List.cons_append]
      rw [denote_lvl_append _ _ _ (by simp)]
      simp only [denote_lvl, List.length_cons]
      rw [show (pre ++ env).length + 1 + 1 - (pre ++ env).length - 1 = 1 by omega]
      simp only [List.getD_cons_succ, List.getD_cons_zero]
      exact (hk.trans_le (hnV pre hp))
    have hys : StableAt w (lvl (pre ++ env).length)
        ((foldAcc w f (pre ++ env) (init.denote w (pre ++ env)) k :: k :: pre) ++ env) :=
      stableAt_lvl (by simp)
    have key := hf _ ⟨_, hsm, rfl⟩ _ _ hx hy hys hyv [] Small.nil
    simp only [List.nil_append, List.cons_append] at key
    exact key.1
  · simp only [denote_foldT]
    exact inv pre hp _ le_rfl

/-- `x ^ i` for `i < V`, given `x ^ V`'s bound in every small extension. -/
theorem t_powT_lt {dx de V : ℕ} (hx : Tm w L dx x env) (hxs : StableAt w x env)
    (he : Tm w L de e env) (hde : de ≤ 32) (heV : Sm w L e V env) (hL : 1 ≤ L) (hd1 : 1 ≤ d)
    (hv : x.denote w env ^ V < 2 ^ (d * L)) (hd : d + dx ≤ 128) (hd32 : d ≤ 32) :
    Tm w L d (powT x e) env := by
  refine t_powT hx hxs he hde hd1 hL (fun pre hp => ?_) hd hd32
  rw [hxs pre]
  rcases Nat.eq_zero_or_pos (x.denote w env) with h0 | hpos
  · rw [h0]
    have := two_le_pow_of hL hd1
    rcases Nat.eq_zero_or_pos (e.denote w (pre ++ env)) with h | h
    · rw [h]; simp; omega
    · rw [zero_pow (by omega)]; omega
  · exact (Nat.pow_le_pow_right hpos (heV pre hp).le).trans_lt hv

/-- `2 ^ i` for `i < V`. -/
theorem t_pow2_lt {de V : ℕ} (he : Tm w L de e env) (hde : de ≤ 32) (heV : Sm w L e V env)
    (hV : V ≤ d * L) (hd : d ≤ 32) (hL : 2 ≤ L) : Tm w L d (pow2 e) env :=
  t_pow2 he hde (fun pre hp => (heV pre hp).trans_le hV) hd hL

/-- A sum whose body may use a bound `V` on the counter. -/
theorem t_sumTv {body : Term → Term} {V : ℕ} (hn : Tm w L dn n env)
    (hnV : ∀ pre, Small L pre → n.denote w (pre ++ env) ≤ V)
    (hb : ∀ env', Ext L env' env → ∀ y, Tm w L dn y env' → StableAt w y env' → Sm w L y V env' →
      Tm w L db (body y) env')
    (hL : 1 ≤ L) (hd : dn + db ≤ 32) : Tm w L (dn + db) (sumT n body) env := by
  refine tm_foldT_inv' hn (by omega) hnV (tm_const (d := 1) (by positivity) (by omega))
    (db := dn + db + 1) (fun env' he x y hx hy hys hyv => ?_) hd (fun pre hp k hk => ?_)
  · exact tm_add hx (hb env' he y hy hys hyv) (by omega) (by omega) (by omega) hL
  · have vn := (hn pre hp).2
    have key : ∀ k ≤ n.denote w (pre ++ env),
        foldAcc w (fun acc i => add acc (body i)) (pre ++ env) ((const 0).denote w (pre ++ env)) k ≤
          k * (2 ^ (db * L) - 1) := by
      intro k hk
      induction k with
      | zero => simp
      | succ k ih =>
        have hacc := ih (by omega)
        rw [foldAcc_succ]
        have hbig : 0 < 2 ^ (db * L) := by positivity
        have hsm : Small L (foldAcc w (fun acc i => add acc (body i)) (pre ++ env)
            ((const 0).denote w (pre ++ env)) k :: k :: pre) := by
          refine Small.cons ?_ (Small.cons ?_ hp)
          · calc _ ≤ k * (2 ^ (db * L) - 1) := hacc
              _ < 2 ^ (dn * L) * 2 ^ (db * L) := by
                  have : k < 2 ^ (dn * L) := by omega
                  calc k * (2 ^ (db * L) - 1) ≤ k * 2 ^ (db * L) :=
                        Nat.mul_le_mul_left _ (Nat.sub_le _ _)
                    _ < 2 ^ (dn * L) * 2 ^ (db * L) := Nat.mul_lt_mul_of_pos_right this hbig
              _ = 2 ^ ((dn + db) * L) := by rw [← pow_add, Nat.add_mul]
              _ ≤ 2 ^ (32 * L) := pow_le_pow_tier hd
          · exact (show k < 2 ^ (dn * L) by omega).trans_le (pow_le_pow_tier (by omega))
        have hy : Tm w L dn (lvl (pre ++ env).length)
            ((foldAcc w (fun acc i => add acc (body i)) (pre ++ env)
              ((const 0).denote w (pre ++ env)) k :: k :: pre) ++ env) := by
          simp only [List.cons_append]; exact tm_second (show k < 2 ^ (dn * L) by omega)
        have hyv : Sm w L (lvl (pre ++ env).length) V
            ((foldAcc w (fun acc i => add acc (body i)) (pre ++ env)
              ((const 0).denote w (pre ++ env)) k :: k :: pre) ++ env) := by
          intro pre' _
          simp only [List.cons_append]
          rw [denote_lvl_append _ _ _ (by simp)]
          simp only [denote_lvl, List.length_cons]
          rw [show (pre ++ env).length + 1 + 1 - (pre ++ env).length - 1 = 1 by omega]
          simp only [List.getD_cons_succ, List.getD_cons_zero]
          exact (show k < n.denote w (pre ++ env) by omega).trans_le (hnV pre hp)
        have hbv := (hb _ ⟨_, hsm, rfl⟩ _ hy (stableAt_lvl (by simp)) hyv).lt
        simp only [List.cons_append] at hbv
        simp only [List.length_append] at hbv
        simp only [denote_add, denote_lvl, List.length_cons, List.length_append]
        rw [show pre.length + env.length + 1 + 1 - (pre.length + env.length + 1) - 1 = 0 by omega,
          List.getD_cons_zero]
        rw [Nat.succ_mul]
        omega
    calc _ ≤ k * (2 ^ (db * L) - 1) := key k hk
      _ < 2 ^ (dn * L) * 2 ^ (db * L) := by
          have : k < 2 ^ (dn * L) := by omega
          have hbig : 0 < 2 ^ (db * L) := by positivity
          calc k * (2 ^ (db * L) - 1) ≤ k * 2 ^ (db * L) := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
            _ < 2 ^ (dn * L) * 2 ^ (db * L) := Nat.mul_lt_mul_of_pos_right this hbig
      _ = 2 ^ ((dn + db) * L) := by rw [← pow_add, Nat.add_mul]

theorem Sm.mono {t : Term} {V V' : ℕ} (h : Sm w L t V env) (hV : V ≤ V') : Sm w L t V' env :=
  fun pre hp => (h pre hp).trans_le hV

variable (w L) in
/-- The value of `t` is at most `V` in every small extension. -/
def Le (t : Term) (V : ℕ) (env : List ℕ) : Prop := ∀ pre, Small L pre → t.denote w (pre ++ env) ≤ V

theorem Le.ext {t : Term} {V : ℕ} (h : Le w L t V env) {env' : List ℕ} (he : Ext L env' env) :
    Le w L t V env' := by
  obtain ⟨p, hp, rfl⟩ := he
  exact fun pre hpre => by rw [← List.append_assoc]; exact h _ (hpre.append hp)

theorem Le.of_tm {t : Term} {d : ℕ} (h : Tm w L d t env) : Le w L t (2 ^ (d * L)) env :=
  fun pre hp => (h pre hp).2.le

theorem Le.of_stable {t : Term} {V : ℕ} (hs : StableAt w t env) (hv : t.denote w env ≤ V) :
    Le w L t V env := fun pre _ => by rw [hs pre]; exact hv

variable (w L) in
/-- A term function maps arguments of tier `da` below `V` to tier `d`. -/
def TmFv (f : Term → Term) (da V d : ℕ) (env : List ℕ) : Prop :=
  ∀ env', Ext L env' env → ∀ x, Tm w L da x env' → StableAt w x env' → Sm w L x V env' →
    Tm w L d (f x) env'

variable (w L) in
/-- A two-argument term function whose first argument is below `V`. -/
def TmF2v (f : Term → Term → Term) (da V db d : ℕ) (env : List ℕ) : Prop :=
  ∀ env', Ext L env' env → ∀ x y, Tm w L da x env' → StableAt w x env' → Sm w L x V env' →
    Tm w L db y env' → StableAt w y env' → Tm w L d (f x y) env'

theorem TmFv.app {f : Term → Term} {da V : ℕ} (h : TmFv w L f da V d env) {env' : List ℕ}
    (he : Ext L env' env) {x : Term} (hx : Tm w L da x env') (hxs : StableAt w x env')
    (hxv : Sm w L x V env') : Tm w L d (f x) env' := h env' he x hx hxs hxv

theorem TmF2v.app {f : Term → Term → Term} {da V db : ℕ} (h : TmF2v w L f da V db d env)
    {env' : List ℕ} (he : Ext L env' env) {x y : Term} (hx : Tm w L da x env')
    (hxs : StableAt w x env') (hxv : Sm w L x V env') (hy : Tm w L db y env')
    (hys : StableAt w y env') : Tm w L d (f x y) env' :=
  h env' he x y hx hxs hxv hy hys

/-- A fold whose body keeps the accumulator's tier, given a bound on the counter. -/
theorem tm_foldTv {init : Term} {f : Term → Term → Term} {V : ℕ}
    (hn : Tm w L dn n env) (hdn : dn ≤ 32) (hnV : Le w L n V env) (hi : Tm w L da init env)
    (hf : ∀ env', Ext L env' env → ∀ x y, Tm w L da x env' → Tm w L dn y env' →
      StableAt w y env' → Sm w L y V env' → Tm w L da (f x y) env') (hda : da ≤ 32) :
    Tm w L da (foldT n init f) env := by
  refine tm_foldT_inv' hn hdn hnV hi hf hda fun pre hp k hk => ?_
  induction k with
  | zero => exact (hi pre hp).2
  | succ k ih =>
    have hacc := ih (by omega)
    have vn := (hn pre hp).2
    have hsm : Small L (foldAcc w f (pre ++ env) (init.denote w (pre ++ env)) k :: k :: pre) :=
      Small.cons (hacc.trans_le (pow_le_pow_tier hda))
        (Small.cons ((show k < 2 ^ (dn * L) by omega).trans_le (pow_le_pow_tier hdn)) hp)
    have hx : Tm w L da (lvl ((pre ++ env).length + 1))
        ((foldAcc w f (pre ++ env) (init.denote w (pre ++ env)) k :: k :: pre) ++ env) := by
      simp only [List.cons_append]
      exact tm_lvl (by simp) (by simp [denote_lvl, hacc])
    have hy : Tm w L dn (lvl (pre ++ env).length)
        ((foldAcc w f (pre ++ env) (init.denote w (pre ++ env)) k :: k :: pre) ++ env) := by
      simp only [List.cons_append]
      exact tm_second (show k < 2 ^ (dn * L) by omega)
    have hyv : Sm w L (lvl (pre ++ env).length) V
        ((foldAcc w f (pre ++ env) (init.denote w (pre ++ env)) k :: k :: pre) ++ env) := by
      intro pre' _
      simp only [List.cons_append]
      rw [denote_lvl_append _ _ _ (by simp)]
      simp only [denote_lvl, List.length_cons]
      rw [show (pre ++ env).length + 1 + 1 - (pre ++ env).length - 1 = 1 by omega]
      simp only [List.getD_cons_succ, List.getD_cons_zero]
      exact (show k < n.denote w (pre ++ env) by omega).trans_le (hnV pre hp)
    have key := hf _ ⟨_, hsm, rfl⟩ _ _ hx hy (stableAt_lvl (by simp)) hyv [] Small.nil
    simp only [List.nil_append, List.cons_append] at key
    rw [foldAcc_succ]
    exact key.2

theorem t_sumModv {p : Term} {body : Term → Term} {dp V : ℕ} (hp : Tm w L dp p env)
    (hpos : Pos w L p env) (hn : Tm w L dn n env) (hnV : Le w L n V env)
    (hb : TmFv w L body dn V db env) (hdp : dp ≤ 32) (hdn : dn ≤ 32)
    (hL : 1 ≤ L) (hd : max dp db + 1 ≤ 128) : Tm w L dp (sumMod p n body) env :=
  tm_foldTv hn hdn hnV (tm_const (by positivity) (by omega)) (fun env' he x y hx hy hys hyv =>
    tm_mod (tm_add hx (hb env' he y hy hys hyv) (by omega) (by omega) hd hL) (hp.ext he)
      (hpos.ext he)) hdp

theorem t_prodModv {p : Term} {body : Term → Term} {dp V : ℕ} (hp : Tm w L dp p env)
    (hpos : Pos w L p env) (hn : Tm w L dn n env) (hnV : Le w L n V env)
    (hb : TmFv w L body dn V db env) (hdp : dp ≤ 32) (hdn : dn ≤ 32)
    (hL : 1 ≤ L) (hdp1 : 1 ≤ dp) (hd : dp + db ≤ 128) : Tm w L dp (prodMod p n body) env :=
  tm_foldTv hn hdn hnV (tm_small_const le_rfl hL hdp1 (by omega)) (fun env' he x y hx hy hys hyv =>
    tm_mod (tm_mul hx (hb env' he y hy hys hyv) le_rfl hd) (hp.ext he) (hpos.ext he)) hdp

theorem t_sumTv' {body : Term → Term} {V : ℕ} (hn : Tm w L dn n env) (hnV : Le w L n V env)
    (hb : TmFv w L body dn V db env) (hL : 1 ≤ L) (hd : dn + db ≤ 32) :
    Tm w L (dn + db) (sumT n body) env :=
  t_sumTv hn hnV (fun env' he y hy hys hyv => hb env' he y hy hys hyv) hL hd

variable (w L) in
/-- A fold body: accumulator of tier `da`, counter of tier `dn` below `V`, result of tier `d`. -/
def TmB (f : Term → Term → Term) (da dn V d : ℕ) (env : List ℕ) : Prop :=
  ∀ env', Ext L env' env → ∀ x y, Tm w L da x env' → Tm w L dn y env' → StableAt w y env' →
    Sm w L y V env' → Tm w L d (f x y) env'

/-- A fold whose body keeps tier `dn + 1` (for example a search returning `j + 1`). -/
theorem t_foldT_closed {init : Term} {f : Term → Term → Term} {di db : ℕ}
    (hn : Tm w L dn n env) (hi : Tm w L di init env)
    (hf : TmB w L f (dn + 1) dn (2 ^ (dn * L)) db env) (hdi : di ≤ dn + 1) (hdb : db ≤ dn + 1)
    (hdn : dn + 1 ≤ 32) : Tm w L (dn + 1) (foldT n init f) env :=
  tm_foldTv hn (by omega) (Le.of_tm hn) (hi.mono hdi)
    (fun env' he x y hx hy hys hyv => (hf env' he x y hx hy hys hyv).mono hdb) hdn

end Cslib.Complexity.NtimeDspace.ProgTerm
