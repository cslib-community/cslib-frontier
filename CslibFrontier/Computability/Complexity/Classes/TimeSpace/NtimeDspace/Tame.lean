/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.ProgPieces

/-!
# Tiers: value bounds that compose

`Tm w L d t env` says: in every extension of `env` by values below `2^(32·L)`,
every value arising in `t` is at most `2^(128·L)` (`Bnd`), and the value of `t`
is below `2^(d·L)`. The number `d` is the tier of `t`. Tiers add under
multiplication, grow by one under addition, and are kept by subtraction,
division and reduction. Bound variables have tier at most `32`.

A fold whose body maps accumulators of tier `a` to results of tier `a` keeps
tier `a` (`tm_foldT`). Folds whose accumulator grows need a stated invariant
(`tm_foldT_inv`). With `L` of order `κ(N)`, the whole counter is bounded by
`2^(128·L)`, which is what `decidable_of_prog_len` needs.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.ProgTerm

open Term

variable {w : List Bool} {L : ℕ}

/-- Values that may be bound in an environment. -/
def Small (L : ℕ) (pre : List ℕ) : Prop := ∀ x ∈ pre, x < 2 ^ (32 * L)

theorem Small.nil : Small L [] := fun _ h => absurd h (List.not_mem_nil)

theorem Small.append {a b : List ℕ} (ha : Small L a) (hb : Small L b) : Small L (a ++ b) :=
  fun x hx => (List.mem_append.mp hx).elim (ha x) (hb x)

theorem Small.cons {x : ℕ} {a : List ℕ} (hx : x < 2 ^ (32 * L)) (ha : Small L a) :
    Small L (x :: a) := fun y hy => (List.mem_cons.mp hy).elim (fun h => h ▸ hx) (ha y)

variable (w L) in
/-- The tier of a term: bounded evaluation and value below `2^(d·L)` in every
small extension of `env`. -/
def Tm (d : ℕ) (t : Term) (env : List ℕ) : Prop :=
  ∀ pre, Small L pre → t.Bnd w (2 ^ (128 * L)) (pre ++ env) ∧ t.denote w (pre ++ env) < 2 ^ (d * L)

variable (L) in
/-- `env'` extends `env` by small values. -/
def Ext (env' env : List ℕ) : Prop := ∃ pre, Small L pre ∧ env' = pre ++ env

theorem Ext.refl (env : List ℕ) : Ext L env env := ⟨[], Small.nil, rfl⟩

theorem Ext.trans {e1 e2 e3 : List ℕ} (h12 : Ext L e1 e2) (h23 : Ext L e2 e3) : Ext L e1 e3 := by
  obtain ⟨p, hp, rfl⟩ := h12
  obtain ⟨q, hq, rfl⟩ := h23
  exact ⟨p ++ q, hp.append hq, (List.append_assoc _ _ _).symm⟩

theorem Ext.cons {x : ℕ} {env' env : List ℕ} (hx : x < 2 ^ (32 * L)) (h : Ext L env' env) :
    Ext L (x :: env') env := by
  obtain ⟨p, hp, rfl⟩ := h
  exact ⟨x :: p, Small.cons hx hp, rfl⟩

variable (w L) in
/-- A one-argument term function maps tier `da` to tier `d`. -/
def TmF (f : Term → Term) (da d : ℕ) (env : List ℕ) : Prop :=
  ∀ env', Ext L env' env → ∀ x, Tm w L da x env' → Tm w L d (f x) env'

variable (w L) in
/-- A two-argument term function maps tiers `da`, `db` to tier `d`. -/
def TmF2 (f : Term → Term → Term) (da db d : ℕ) (env : List ℕ) : Prop :=
  ∀ env', Ext L env' env → ∀ x y, Tm w L da x env' → Tm w L db y env' → Tm w L d (f x y) env'

variable (w L) in
/-- A three-argument term function maps tiers `da`, `db`, `dc` to tier `d`. -/
def TmF3 (f : Term → Term → Term → Term) (da db dc d : ℕ) (env : List ℕ) : Prop :=
  ∀ env', Ext L env' env → ∀ x y z, Tm w L da x env' → Tm w L db y env' → Tm w L dc z env' →
    Tm w L d (f x y z) env'

variable {d d' d1 d2 : ℕ} {a b c t e i : Term} {env : List ℕ}

theorem pow_le_pow_tier {x y : ℕ} (h : x ≤ y) : 2 ^ (x * L) ≤ 2 ^ (y * L) :=
  Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ h)

theorem Tm.extend (h : Tm w L d t env) {pre : List ℕ} (hp : Small L pre) :
    Tm w L d t (pre ++ env) := fun pre' hp' => by
  rw [← List.append_assoc]; exact h _ (hp'.append hp)

theorem Tm.mono (h : Tm w L d t env) (hd : d ≤ d') : Tm w L d' t env := fun pre hp =>
  ⟨(h pre hp).1, (h pre hp).2.trans_le (pow_le_pow_tier hd)⟩

theorem Tm.bnd (h : Tm w L d t env) : t.Bnd w (2 ^ (128 * L)) env := (h [] Small.nil).1

theorem Tm.lt (h : Tm w L d t env) : t.denote w env < 2 ^ (d * L) := (h [] Small.nil).2

theorem Tm.ext (h : Tm w L d t env) {env' : List ℕ} (he : Ext L env' env) : Tm w L d t env' := by
  obtain ⟨p, hp, rfl⟩ := he; exact h.extend hp

theorem Tm.ext_mono (h : Tm w L d t env) {env' : List ℕ} (he : Ext L env' env) (hd : d ≤ d') :
    Tm w L d' t env' := (h.ext he).mono hd

theorem TmF.ext {f : Term → Term} {da : ℕ} (h : TmF w L f da d env) {env' : List ℕ}
    (he : Ext L env' env) : TmF w L f da d env' := fun e2 h2 x hx => h e2 (h2.trans he) x hx

theorem TmF2.ext {f : Term → Term → Term} {da db : ℕ} (h : TmF2 w L f da db d env)
    {env' : List ℕ} (he : Ext L env' env) : TmF2 w L f da db d env' :=
  fun e2 h2 x y hx hy => h e2 (h2.trans he) x y hx hy

theorem TmF3.ext {f : Term → Term → Term → Term} {da db dc : ℕ} (h : TmF3 w L f da db dc d env)
    {env' : List ℕ} (he : Ext L env' env) : TmF3 w L f da db dc d env' :=
  fun e2 h2 x y z hx hy hz => h e2 (h2.trans he) x y z hx hy hz

theorem TmF.app {f : Term → Term} {da : ℕ} (h : TmF w L f da d env) {env' : List ℕ}
    (he : Ext L env' env) {x : Term} (hx : Tm w L da x env') : Tm w L d (f x) env' := h env' he x hx

theorem TmF2.app {f : Term → Term → Term} {da db : ℕ} (h : TmF2 w L f da db d env)
    {env' : List ℕ} (he : Ext L env' env) {x y : Term} (hx : Tm w L da x env')
    (hy : Tm w L db y env') : Tm w L d (f x y) env' := h env' he x y hx hy

theorem TmF3.app {f : Term → Term → Term → Term} {da db dc : ℕ} (h : TmF3 w L f da db dc d env)
    {env' : List ℕ} (he : Ext L env' env) {x y z : Term} (hx : Tm w L da x env')
    (hy : Tm w L db y env') (hz : Tm w L dc z env') : Tm w L d (f x y z) env' :=
  h env' he x y z hx hy hz

/-! ### Leaves -/

theorem denote_lvl_append (l : ℕ) (pre env : List ℕ) (h : l < env.length) :
    (lvl l).denote w (pre ++ env) = (lvl l).denote w env := by
  simp only [denote_lvl, List.length_append]
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    show pre.length + env.length - l - 1 = pre.length + (env.length - l - 1) by omega,
    List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]

theorem tm_lvl {l : ℕ} (h : l < env.length) (hv : (lvl l).denote w env < 2 ^ (d * L)) :
    Tm w L d (lvl l) env := fun pre _ => ⟨trivial, by rw [denote_lvl_append l pre env h]; exact hv⟩

/-- The variable bound on top of `env`. -/
theorem tm_top {x : ℕ} (hx : x < 2 ^ (d * L)) : Tm w L d (lvl env.length) (x :: env) :=
  tm_lvl (by simp) (by simp [denote_lvl, hx])

/-- The variable bound second from the top. -/
theorem tm_second {x y : ℕ} (hy : y < 2 ^ (d * L)) :
    Tm w L d (lvl env.length) (x :: y :: env) :=
  tm_lvl (by simp) (by
    simp only [denote_lvl, List.length_cons]
    rw [show env.length + 1 + 1 - env.length - 1 = 1 by omega]; simpa using hy)

theorem tm_const {k : ℕ} (hk : k < 2 ^ (d * L)) (hd : d ≤ 128) : Tm w L d (const k) env :=
  fun _ _ => ⟨hk.le.trans (pow_le_pow_tier hd), hk⟩

theorem two_le_pow_of {L d : ℕ} (hL : 1 ≤ L) (hd : 1 ≤ d) : 2 ≤ 2 ^ (d * L) := by
  have : 1 ≤ d * L := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  calc 2 = 2 ^ 1 := rfl
    _ ≤ 2 ^ (d * L) := Nat.pow_le_pow_right (by norm_num) this

theorem tm_small_const {k : ℕ} (hk : k ≤ 1) (hL : 1 ≤ L) (hd : 1 ≤ d) (hd' : d ≤ 128) :
    Tm w L d (const k) env :=
  tm_const (by have := two_le_pow_of hL hd; omega) hd'

/-! ### Operations -/

theorem tm_add (ha : Tm w L d1 a env) (hb : Tm w L d2 b env) (h1 : d1 + 1 ≤ d) (h2 : d2 + 1 ≤ d)
    (hd : d ≤ 128) (hL : 1 ≤ L) : Tm w L d (add a b) env := fun pre hp => by
  obtain ⟨ba, va⟩ := ha pre hp
  obtain ⟨bb, vb⟩ := hb pre hp
  have hsum : a.denote w (pre ++ env) + b.denote w (pre ++ env) < 2 ^ (d * L) := by
    have e1 := pow_le_pow_tier (L := L) (show d1 ≤ d - 1 by omega)
    have e2 := pow_le_pow_tier (L := L) (show d2 ≤ d - 1 by omega)
    have : 2 ^ ((d - 1) * L) * 2 ≤ 2 ^ (d * L) := by
      rw [← pow_succ]; exact Nat.pow_le_pow_right (by norm_num) (by
        rw [Nat.sub_mul, Nat.one_mul]; have : L ≤ d * L := Nat.le_mul_of_pos_left _ (by omega)
        omega)
    omega
  exact ⟨⟨ba, bb, (hsum.le.trans (pow_le_pow_tier hd))⟩, hsum⟩

theorem tm_mul (ha : Tm w L d1 a env) (hb : Tm w L d2 b env) (h : d1 + d2 ≤ d) (hd : d ≤ 128) :
    Tm w L d (mul a b) env := fun pre hp => by
  obtain ⟨ba, va⟩ := ha pre hp
  obtain ⟨bb, vb⟩ := hb pre hp
  have hprod : a.denote w (pre ++ env) * b.denote w (pre ++ env) < 2 ^ (d * L) := by
    calc a.denote w (pre ++ env) * b.denote w (pre ++ env)
        < 2 ^ (d1 * L) * 2 ^ (d2 * L) := Nat.mul_lt_mul'' va vb
      _ = 2 ^ ((d1 + d2) * L) := by rw [← pow_add, Nat.add_mul]
      _ ≤ 2 ^ (d * L) := pow_le_pow_tier h
  exact ⟨⟨ba, bb, hprod.le.trans (pow_le_pow_tier hd)⟩, hprod⟩

theorem tm_sub (ha : Tm w L d a env) (hb : Tm w L d' b env) : Tm w L d (sub a b) env :=
  fun pre hp => ⟨⟨(ha pre hp).1, (hb pre hp).1⟩, (Nat.sub_le _ _).trans_lt (ha pre hp).2⟩

theorem tm_div (ha : Tm w L d a env) (hb : Tm w L d' b env) : Tm w L d (div a b) env :=
  fun pre hp => ⟨⟨(ha pre hp).1, (hb pre hp).1⟩, (Nat.div_le_self _ _).trans_lt (ha pre hp).2⟩

theorem tm_mod_left (ha : Tm w L d a env) (hb : Tm w L d' b env) : Tm w L d (mod a b) env :=
  fun pre hp => ⟨⟨(ha pre hp).1, (hb pre hp).1⟩, (Nat.mod_le _ _).trans_lt (ha pre hp).2⟩

variable (w L) in
/-- A term that is positive in every small extension. -/
def Pos (t : Term) (env : List ℕ) : Prop := ∀ pre, Small L pre → 0 < t.denote w (pre ++ env)

theorem Pos.ext (h : Pos w L t env) {env' : List ℕ} (he : Ext L env' env) : Pos w L t env' := by
  obtain ⟨p, hp, rfl⟩ := he
  exact fun pre' hp' => by rw [← List.append_assoc]; exact h _ (hp'.append hp)

theorem Pos.of_stable (hs : StableAt w t env) (hv : 0 < t.denote w env) : Pos w L t env :=
  fun pre _ => by rw [hs pre]; exact hv

theorem tm_mod (ha : Tm w L d' a env) (hb : Tm w L d b env) (hpos : Pos w L b env) :
    Tm w L d (mod a b) env :=
  fun pre hp => ⟨⟨(ha pre hp).1, (hb pre hp).1⟩, (Nat.mod_lt _ (hpos pre hp)).trans (hb pre hp).2⟩

theorem tm_bit (ha : Tm w L d1 a env) (hi : Tm w L d2 i env) (hL : 1 ≤ L) (hd : 1 ≤ d) :
    Tm w L d (bit a i) env := fun pre hp => by
  refine ⟨⟨(ha pre hp).1, (hi pre hp).1⟩, ?_⟩
  have := two_le_pow_of hL hd
  simp only [denote_bit]
  cases Nat.testBit _ _ <;> simp; omega

theorem tm_lt (ha : Tm w L d1 a env) (hb : Tm w L d2 b env) (hL : 1 ≤ L) (hd : 1 ≤ d) :
    Tm w L d (lt a b) env := fun pre hp => by
  refine ⟨⟨(ha pre hp).1, (hb pre hp).1⟩, ?_⟩
  have := two_le_pow_of hL hd
  simp only [denote_lt]
  split_ifs <;> omega

theorem tm_input (ha : Tm w L d1 a env) (hL : 2 ≤ L) (hd : 1 ≤ d) : Tm w L d (input a) env :=
  fun pre hp => by
  refine ⟨(ha pre hp).1, ?_⟩
  have h4 : 4 ≤ 2 ^ (d * L) := by
    calc 4 = 2 ^ 2 := rfl
      _ ≤ 2 ^ (d * L) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  simp only [denote_input, ProgLang.Prog.inputValue]
  split <;> omega

theorem tm_ite (hc : Tm w L d1 c env) (ht : Tm w L d t env) (he : Tm w L d e env) :
    Tm w L d (ite c t e) env := fun pre hp => by
  refine ⟨⟨(hc pre hp).1, ?_⟩, ?_⟩
  · split_ifs
    · exact (ht pre hp).1
    · exact (he pre hp).1
  · simp only [denote_ite]
    split_ifs
    · exact (ht pre hp).2
    · exact (he pre hp).2

/-! ### Binders -/

theorem tm_letT {f : Term → Term} {da : ℕ} (ha : Tm w L da a env) (hda : da ≤ 32)
    (hf : TmF w L f da d env) : Tm w L d (letT a f) env := fun pre hp => by
  obtain ⟨ba, va⟩ := ha pre hp
  have hsm : Small L (a.denote w (pre ++ env) :: pre) :=
    Small.cons (va.trans_le (pow_le_pow_tier hda)) hp
  have hx : Tm w L da (lvl (pre ++ env).length) ((a.denote w (pre ++ env) :: pre) ++ env) := by
    rw [List.cons_append]; exact tm_top va
  have key := hf _ ⟨_, hsm, rfl⟩ _ hx [] Small.nil
  simp only [List.nil_append, List.cons_append] at key
  exact ⟨⟨ba, key.1⟩, key.2⟩

/-- A fold whose accumulator stays below a stated tier. -/
theorem tm_foldT_inv {n init : Term} {f : Term → Term → Term} {dn di da db : ℕ}
    (hn : Tm w L dn n env) (hdn : dn ≤ 32) (hi : Tm w L di init env)
    (hf : TmF2 w L f da dn db env) (hda : da ≤ 32)
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
    have key := hf _ ⟨_, hsm, rfl⟩ _ _ hx hy [] Small.nil
    simp only [List.nil_append, List.cons_append] at key
    exact key.1
  · simp only [denote_foldT]
    exact inv pre hp _ le_rfl

/-- A fold whose body keeps the accumulator's tier. -/
theorem tm_foldT {n init : Term} {f : Term → Term → Term} {dn da : ℕ}
    (hn : Tm w L dn n env) (hdn : dn ≤ 32) (hi : Tm w L da init env)
    (hf : TmF2 w L f da dn da env) (hda : da ≤ 32) :
    Tm w L da (foldT n init f) env := by
  refine tm_foldT_inv hn hdn hi hf hda fun pre hp k hk => ?_
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
    have key := hf _ ⟨_, hsm, rfl⟩ _ _ hx hy [] Small.nil
    simp only [List.nil_append, List.cons_append] at key
    rw [foldAcc_succ]
    exact key.2

end Cslib.Complexity.NtimeDspace.ProgTerm
