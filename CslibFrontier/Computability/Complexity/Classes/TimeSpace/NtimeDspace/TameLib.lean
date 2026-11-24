/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Tame
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.WeightTerm

/-!
# Exact-tier lemmas and the `tame` tactic

Each `t_*` lemma gives a combinator the tier computed from its arguments'
tiers. `tame` proves `Tm`, `TmF`, `TmF2`, `TmF3` and `Pos` goals by using
hypotheses, applying these lemmas, and unfolding definitions; it leaves the
numeric side conditions to `omega`, and stops at folds that need an
invariant (`pow2`, `powT`, raw `foldT`), which are proved separately.
-/

public section

namespace Cslib.Complexity.NtimeDspace.ProgTerm

open Term

variable {w : List Bool} {L : ℕ} {d1 d2 da db dn dp : ℕ} {a b c t e i n p : Term} {env : List ℕ}

theorem t_const {k : ℕ} (hk : k < 2 ^ L) : Tm w L 1 (const k) env :=
  tm_const (by simpa using hk) (by norm_num)

theorem t_add (ha : Tm w L d1 a env) (hb : Tm w L d2 b env) (hL : 1 ≤ L)
    (hd : max d1 d2 + 1 ≤ 128) : Tm w L (max d1 d2 + 1) (add a b) env :=
  tm_add ha hb (by omega) (by omega) hd hL

theorem t_mul (ha : Tm w L d1 a env) (hb : Tm w L d2 b env) (hd : d1 + d2 ≤ 128) :
    Tm w L (d1 + d2) (mul a b) env := tm_mul ha hb le_rfl hd

theorem t_sub (ha : Tm w L d1 a env) (hb : Tm w L d2 b env) : Tm w L d1 (sub a b)
    env := tm_sub ha hb
theorem t_div (ha : Tm w L d1 a env) (hb : Tm w L d2 b env) : Tm w L d1 (div a b)
    env := tm_div ha hb
theorem t_mod (ha : Tm w L d1 a env) (hb : Tm w L d2 b env) (hpos : Pos w L b env) :
    Tm w L d2 (mod a b) env := tm_mod ha hb hpos
theorem t_mod_left (ha : Tm w L d1 a env) (hb : Tm w L d2 b env) : Tm w L d1 (mod a b) env :=
  tm_mod_left ha hb
theorem t_bit (ha : Tm w L d1 a env) (hi : Tm w L d2 i env) (hL : 1 ≤ L) : Tm w L 1 (bit a i) env :=
  tm_bit ha hi hL le_rfl
theorem t_lt (ha : Tm w L d1 a env) (hb : Tm w L d2 b env) (hL : 1 ≤ L) : Tm w L 1 (lt a b) env :=
  tm_lt ha hb hL le_rfl
theorem t_input (ha : Tm w L d1 a env) (hL : 2 ≤ L) : Tm w L 1 (input a) env :=
    tm_input ha hL le_rfl
theorem t_ite (hc : Tm w L d1 c env) (ht : Tm w L da t env) (he : Tm w L db e env) :
    Tm w L (max da db) (ite c t e) env :=
  tm_ite hc (ht.mono (le_max_left _ _)) (he.mono (le_max_right _ _))
theorem t_letT {f : Term → Term} {d : ℕ} (ha : Tm w L da a env) (hda : da ≤ 32)
    (hf : TmF w L f da d env) : Tm w L d (letT a f) env := tm_letT ha hda hf

theorem t_sumMod {body : Term → Term} (hp : Tm w L dp p env) (hpos : Pos w L p env)
    (hn : Tm w L dn n env) (hb : TmF w L body dn db env) (hdp : dp ≤ 32) (hdn : dn ≤ 32)
    (hL : 1 ≤ L) (hd : max dp db + 1 ≤ 128) : Tm w L dp (sumMod p n body) env := by
  refine tm_foldT hn hdn (tm_const (by positivity) (by omega)) (fun env' he x y hx hy => ?_) hdp
  exact tm_mod (tm_add hx (hb.app he hy) (by omega) (by omega) hd hL) (hp.ext he) (hpos.ext he)

theorem t_prodMod {body : Term → Term} (hp : Tm w L dp p env) (hpos : Pos w L p env)
    (hn : Tm w L dn n env) (hb : TmF w L body dn db env) (hdp : dp ≤ 32) (hdn : dn ≤ 32)
    (hL : 1 ≤ L) (hdp1 : 1 ≤ dp) (hd : dp + db ≤ 128) : Tm w L dp (prodMod p n body) env := by
  refine tm_foldT hn hdn (tm_small_const le_rfl hL hdp1 (by omega))
      (fun env' he x y hx hy => ?_) hdp
  exact tm_mod (tm_mul hx (hb.app he hy) le_rfl hd) (hp.ext he) (hpos.ext he)

/-- A modular fold keeps just one residue accumulator, including Horner evaluation. -/
theorem t_foldModT {body : Term → Term → Term}
    (hp : Tm w L dp p env) (hpos : Pos w L p env) (hn : Tm w L dn n env)
    (hb : TmF2 w L body dp dn db env) (hdp : dp ≤ 32) (hdn : dn ≤ 32)
    (hL : 1 ≤ L) (hdp1 : 1 ≤ dp) : Tm w L dp (foldModT p n body) env := by
  refine tm_foldT hn hdn (tm_small_const (by omega) hL hdp1 (by omega))
    (fun env' he x y hx hy => ?_) hdp
  exact tm_mod (hb.app he hx hy) (hp.ext he) (hpos.ext he)

theorem t_sumT {body : Term → Term} (hn : Tm w L dn n env) (hb : TmF w L body dn db env)
    (hL : 1 ≤ L) (hd : dn + db ≤ 32) : Tm w L (dn + db) (sumT n body) env := by
  refine tm_foldT_inv hn (by omega) (tm_const (d := 1) (by positivity) (by omega))
    (db := dn + db + 1) (fun env' he x y hx hy => ?_) hd (fun pre hp k hk => ?_)
  · exact tm_add hx (hb.app he hy) (by omega) (by omega) (by omega) hL
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
        have hbv := (hb _ ⟨_, hsm, rfl⟩ _ hy).lt
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

/-- `T / x^i` by repeated division keeps the tier of `T`. -/
theorem t_divPowT {x T : Term} {dx dT di : ℕ} (hx : Tm w L dx x env) (hT : Tm w L dT T env)
    (hi : Tm w L di i env) (hdi : di ≤ 32) (hdT : dT ≤ 32) : Tm w L dT (divPowT x T i) env :=
  tm_foldT hi hdi hT (fun _ he _ _ ha _ => tm_div ha (hx.ext he)) hdT

theorem Pos.const' {k : ℕ} (hk : 0 < k) : Pos w L (const k) env := fun _ _ => hk
theorem Pos.mul' (ha : Pos w L a env) (hb : Pos w L b env) : Pos w L (mul a b) env :=
  fun pre hp => Nat.mul_pos (ha pre hp) (hb pre hp)
theorem Pos.add_right' (hb : Pos w L b env) : Pos w L (add a b) env :=
  fun pre hp => Nat.add_pos_right _ (hb pre hp)
theorem Pos.add_left' (ha : Pos w L a env) : Pos w L (add a b) env :=
  fun pre hp => Nat.add_pos_left (ha pre hp) _
theorem Pos.pow2' : Pos w L (pow2 e) env := fun pre _ => by rw [denote_pow2]; positivity

/-- Literals are below `2 ^ L` once `L ≥ 2`. -/
theorem lit_lt_two_pow {k : ℕ} (hk : k ≤ 3) (hL : 2 ≤ L) : k < 2 ^ L :=
  lt_of_le_of_lt hk (by
    calc 3 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) hL)

theorem lit_lt_two_pow_big {k : ℕ} (hk : k ≤ 255) (hL : 8 ≤ L) : k < 2 ^ L :=
  lt_of_le_of_lt hk (by
    calc 255 < 2 ^ 8 := by norm_num
      _ ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) hL)

theorem lit_lt_two_pow' {k : ℕ} (hk : k ≤ 3) (hL : 2 ≤ L) : k < 2 ^ L := lit_lt_two_pow hk hL

/-- `2 ^ e`, given a bound on the exponent in every small extension. -/
theorem t_pow2 {d de : ℕ} (he : Tm w L de e env) (hde : de ≤ 32)
    (hv : ∀ pre, Small L pre → e.denote w (pre ++ env) < d * L) (hd : d ≤ 32) (hL : 2 ≤ L) :
    Tm w L d (pow2 e) env := by
  refine tm_foldT_inv he hde (tm_const (d := 1)
      (by simpa using lit_lt_two_pow' (k := 1) (by omega) hL)
    (by omega)) (db := d + 1)
    (fun env' he' x y hx hy => tm_mul hx (tm_const (d := 1)
      (by simpa using lit_lt_two_pow' (k := 2) (by omega) hL) (by omega))
      le_rfl (by omega)) hd (fun pre hp k hk => ?_)
  have := foldAcc_pow2 (w := w) (pre ++ env) k
  rw [denote_const, this]
  exact Nat.pow_lt_pow_right (by norm_num) ((hk.trans_lt (hv pre hp)))

theorem t_pow2_stable {d de : ℕ} (he : Tm w L de e env) (hde : de ≤ 32) (hs : StableAt w e env)
    (hv : e.denote w env < d * L) (hd : d ≤ 32) (hL : 2 ≤ L) : Tm w L d (pow2 e) env :=
  t_pow2 he hde (fun pre _ => by rw [hs pre]; exact hv) hd hL

/-- `x ^ e` for a stable base, given a bound on the power. -/
theorem t_powT {x : Term} {d dx de : ℕ} (hx : Tm w L dx x env) (hxs : StableAt w x env)
    (he : Tm w L de e env) (hde : de ≤ 32) (hd1 : 1 ≤ d) (hL : 1 ≤ L)
    (hv : ∀ pre, Small L pre → x.denote w (pre ++ env) ^ e.denote w (pre ++ env) < 2 ^ (d * L))
    (hd : d + dx ≤ 128) (hd32 : d ≤ 32) : Tm w L d (powT x e) env := by
  refine tm_foldT_inv he hde (tm_small_const (d := 1) le_rfl hL le_rfl (by omega)) (db := d + dx)
    (fun env' he' y z hy hz => tm_mul hy (hx.ext he') le_rfl hd) hd32 (fun pre hp k hk => ?_)
  have hval := powT_denote (w := w) x (const k) (pre ++ env) (hxs.extend pre)
  simp only [powT, denote_foldT, denote_const] at hval ⊢
  rw [hval]
  rcases Nat.eq_zero_or_pos (x.denote w (pre ++ env)) with h0 | hpos
  · rw [h0]
    have := two_le_pow_of hL hd1
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · subst hk0; simp; omega
    · rw [zero_pow (by omega)]; omega
  · exact (Nat.pow_le_pow_right hpos hk).trans_lt (hv pre hp)


end Cslib.Complexity.NtimeDspace.ProgTerm
