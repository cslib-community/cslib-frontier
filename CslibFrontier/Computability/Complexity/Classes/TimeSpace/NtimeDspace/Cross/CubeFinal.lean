/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.ColumnAdder
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.CubeStatement
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.GenPar
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.GenSize

/-!
# Theorem 2.3 in bit form, by the walks on the cube

`cubeCounting : CubeCounting` is Theorem 2.3 (`thm:counting`) in bit form for every family of
networks with logspace access, and `cubeBlockBits : Exact.BlockBits` gives the bits of the
contractions of the block networks of Lemma 2.2, from which `ColumnAdder.lean` adds up the accept
count. Both run the evaluator `formulaBitT` of `GenBits.lean` (Proposition 3.2 on the programs of
the formula of §6.2) at a parameter computed from the environment:

* the size `s` (the clock `τ` for the block networks), the bit index `j` (`P = j + 1`), the field
  width `fw = 3 (⌊log₂ s⌋ + 1) + 5`, the number `K = 2^(h_* - 1)` of vertex groups, and the budget
  `L = c_L · SqrtLog s`, which is also the reader fuel and the fuel of the unfolding;
* for the block networks also `|w|`, `τ` and the schedule `σ`.

Bits beyond the size of `Z(G)` are answered `0` directly: `j ≥ E = (C + 1)(s + 2)^(C + 2)` for a
family (`CubeCounting.toNat_value_lt`), `j ≥ 2τ` for a block network (the contraction is at most
the accept count, at most `2^(paddedTime τ)` with `paddedTime τ + 1 ≤ 2τ`), so the precision stays
polynomial. The evaluator is correct with every value below `2^(128 L)` by `cube_bit_size` of
`GenSize.lean`; the parameter terms have values below `2^L`.

## Main definitions

* `CubeFinal.famProg F cL`: the program over `[s, |w|, j]`.
* `CubeFinal.blockProg M e cL`: the program over `[τ, |w|, σ, j]`.

## Main results

* `cubeCounting : CubeCounting`.
* `cubeBlockBits : Exact.BlockBits`.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Cross

open NtimeDspace.ProgLang NtimeDspace.ProgTerm Term NtimeDspace.SumProduct NtimeDspace.Cross.Exact

namespace CubeFinal

variable {w : List Bool} {env : List ℕ} {M : ℕ} {x : Term} {a : ℕ}

/-! ### Between the toolkits -/

theorem numVal {t : Term} {v : ℕ} (h : Val w t env v) : Cube.Num.Val w env t v :=
  ⟨fun extra => (h extra).trans h.eq.symm, h.eq⟩

theorem tm_of {L : ℕ} {t : Term} {v : ℕ} (hb : Bd w (2 ^ (128 * L)) t env) (hv : Val w t env v)
    (hlt : v < 2 ^ L) : Tm w L 1 t env := fun pre
        _ => ⟨hb pre, (hv pre).trans_lt (by rwa [one_mul])⟩

/-! ### The sizes as terms -/

/-- `⌊log₂ x⌋`, for `x ≥ 1`. -/
def lgT (x : Term) : Term := sub (bitLenT x) (const 1)

theorem val_lgT (hx : Val w x env a) (ha : 1 ≤ a) : Val w (lgT x) env (Nat.log 2 a) := by
  have := val_sub (val_bitLenT hx ha) (val_const 1 env)
  rwa [Nat.add_sub_cancel] at this

theorem bd_lgT (hx : Val w x env a) (hbx : Bd w M x env) (ha : a + 1 ≤ M) : Bd w M (lgT x) env :=
  bd_sub (bd_bitLenT hx hbx ha) (bd_const (by omega) _)

/-- The field width `3 (⌊log₂ x⌋ + 1) + 5`. -/
def fwT (x : Term) : Term := add (mul (const 3) (bitLenT x)) (const 5)

theorem val_fwT (hx : Val w x env a) (ha : 1 ≤ a) :
    Val w (fwT x) env (3 * (Nat.log 2 a + 1) + 5) :=
  val_add (val_mul (val_const 3 env) (val_bitLenT hx ha)) (val_const 5 env)

theorem bd_fwT (hx : Val w x env a) (hbx : Bd w M x env) (ha : 1 ≤ a) (hM : 4 * a + 8 ≤ M) :
    Bd w M (fwT x) env := by
  have hl : Nat.log 2 a < a := Nat.log_lt_self 2 (by omega)
  exact bd_add (bd_mul (bd_const (by omega) _) (bd_bitLenT hx hbx (by omega)) (val_const 3 env)
    (val_bitLenT hx ha) (by omega)) (bd_const (by omega) _)
    (val_mul (val_const 3 env) (val_bitLenT hx ha)) (val_const 5 env) (by omega)

/-- `h_* = 2^⌊log₂ (⌊log₂ x⌋ / 3)⌋` (`Cube.hstar`). -/
def hstarT (x : Term) : Term := pwT (const 2) (lgT (div (lgT x) (const 3)))

theorem one_le_of_log {a : ℕ} (ha : 3 ≤ Nat.log 2 a) : 1 ≤ a := by
  rcases Nat.eq_zero_or_pos a with h | h
  · subst h; simp at ha
  · exact h

theorem hstar_le {a : ℕ} (ha : 3 ≤ Nat.log 2 a) : Cube.hstar a ≤ Nat.log 2 a / 3 :=
  Nat.pow_log_le_self 2 (by omega)

theorem val_hstarT (hx : Val w x env a) (ha : 3 ≤ Nat.log 2 a) :
    Val w (hstarT x) env (Cube.hstar a) :=
  val_pwT (val_const 2 env) (val_lgT (val_div (val_lgT hx (one_le_of_log ha)) (val_const 3 env))
    (by omega))

theorem bd_hstarT (hx : Val w x env a) (hbx : Bd w M x env) (ha : 3 ≤ Nat.log 2 a)
    (hM : 2 * a + 2 ≤ M) : Bd w M (hstarT x) env := by
  have h1 := one_le_of_log ha
  have hl : Nat.log 2 a < a := Nat.log_lt_self 2 (by omega)
  have hp : 2 ^ Nat.log 2 a ≤ a := Nat.pow_log_le_self 2 (by omega)
  have hll : Nat.log 2 (Nat.log 2 a / 3) ≤ Nat.log 2 a / 3 :=
    (Nat.log_lt_self 2 (by omega)).le
  have vl := val_lgT hx h1
  refine bd_pwT (val_const 2 env) (val_lgT (val_div vl (val_const 3 env)) (by omega))
    (bd_const (by omega) _) (bd_lgT (val_div vl (val_const 3 env))
      (bd_div (bd_lgT hx hbx (by omega)) (bd_const (by omega) _)) (by omega))
    (k := Nat.log 2 a) (by omega) (by omega) (by norm_num) (by omega)

/-- `K = 2^(h_* - 1)`. -/
def kT (x : Term) : Term := pwT (const 2) (sub (hstarT x) (const 1))

theorem val_kT (hx : Val w x env a) (ha : 3 ≤ Nat.log 2 a) :
    Val w (kT x) env (2 ^ (Cube.hstar a - 1)) :=
  val_pwT (val_const 2 env) (val_sub (val_hstarT hx ha) (val_const 1 env))

theorem kT_le {a : ℕ} (ha : 3 ≤ Nat.log 2 a) : 2 ^ (Cube.hstar a - 1) ≤ a :=
  (Nat.pow_le_pow_right (by norm_num) (by have := hstar_le ha; omega)).trans
    (Nat.pow_log_le_self 2 (by have := one_le_of_log ha; omega))

theorem bd_kT (hx : Val w x env a) (hbx : Bd w M x env) (ha : 3 ≤ Nat.log 2 a)
    (hM : 2 * a + 2 ≤ M) : Bd w M (kT x) env := by
  have h1 := one_le_of_log ha
  have hl : Nat.log 2 a < a := Nat.log_lt_self 2 (by omega)
  have hh := hstar_le ha
  have hp : 2 ^ Nat.log 2 a ≤ a := Nat.pow_log_le_self 2 (by omega)
  exact bd_pwT (val_const 2 env) (val_sub (val_hstarT hx ha) (val_const 1 env))
    (bd_const (by omega) _) (bd_sub (bd_hstarT hx hbx ha hM) (bd_const (by omega) _))
    (k := Nat.log 2 a) (by omega) (by omega) (by norm_num) (by omega)

/-- The budget `c · SqrtLog x`. -/
def bLT (c : ℕ) (x : Term) : Term := mul (const c) (sqrtLogT' x)

theorem val_bLT (c : ℕ) (hx : Val w x env a) (ha : 1 ≤ a) : Val w (bLT c x) env (c * SqrtLog a) :=
  val_mul (val_const c env) (val_sqrtLogT' hx ha)

theorem bd_bLT (c : ℕ) (hx : Val w x env a) (hbx : Bd w M x env) (ha : 1 ≤ a)
    (hM : (a + 2) * (a + 2) ≤ M) (hc : c * SqrtLog a ≤ M) (hc1 : 1 ≤ SqrtLog a) :
    Bd w M (bLT c x) env :=
  bd_mul (bd_const (le_trans (Nat.le_mul_of_pos_right _ hc1) hc) _) (bd_sqrtLogT' hx hbx ha hM)
    (val_const c env) (val_sqrtLogT' hx ha) hc

/-- `E = (C + 1)(x + 2)^(C + 2)` (`CubeCounting.expE`). -/
def expT' (C : ℕ) (x : Term) : Term := mul (const (C + 1)) (pwT (add x (const 2)) (const (C + 2)))

theorem val_expT' (C : ℕ) (hx : Val w x env a) : Val w (expT' C x) env (CubeCounting.expE C a) :=
  val_mul (val_const _ env) (val_pwT (val_add hx (val_const 2 env)) (val_const _ env))

theorem bd_expT' (C : ℕ) (hx : Val w x env a) (hbx : Bd w M x env)
    (hM : (C + 2) * (a + 2) ^ (C + 2) ≤ M) : Bd w M (expT' C x) env := by
  have h1 : 1 ≤ (a + 2) ^ (C + 2) := Nat.one_le_pow _ _ (by omega)
  have h2 : a + 2 ≤ (a + 2) ^ (C + 2) := Nat.le_self_pow (by omega) _
  have h3 : (a + 2) ^ (C + 2) ≤ (C + 2) * (a + 2) ^ (C + 2) := Nat.le_mul_of_pos_left _ (by omega)
  have h4 : C + 2 ≤ (C + 2) * (a + 2) ^ (C + 2) := Nat.le_mul_of_pos_right _ h1
  have h5 : (C + 1) * (a + 2) ^ (C + 2) ≤ (C + 2) * (a + 2) ^ (C + 2) :=
    Nat.mul_le_mul_right _ (by omega)
  exact bd_mul (bd_const (by omega) _) (bd_pwT (val_add hx (val_const 2 env)) (val_const _ env)
      (bd_add hbx (bd_const (by omega) _) hx (val_const 2 env) (by omega)) (bd_const (by omega) _)
      le_rfl (by omega) (by omega) (by omega))
    (val_const _ env) (val_pwT (val_add hx (val_const 2 env)) (val_const _ env)) (by omega)

/-! ### The size terms at the budget -/

/-- **The size terms** at a size `a` with `⌊log₂ a⌋ ≥ 3`, the budget `L = c · SqrtLog a` with
`c ≥ 8`, and the bound `2^(128 L)`: their values and bounds, and the values below `2^L`. -/
theorem size_terms {c L : ℕ} (hx : Val w x env a) (hbx : Bd w (2 ^ (128 * L)) x env)
    (ha : 3 ≤ Nat.log 2 a) (hc : 8 ≤ c) (hL : L = c * SqrtLog a) :
    Val w (bLT c x) env L ∧ Bd w (2 ^ (128 * L)) (bLT c x) env ∧
      Val w (fwT x) env (3 * (Nat.log 2 a + 1) + 5) ∧ Bd w (2 ^ (128 * L)) (fwT x) env ∧
      Val w (kT x) env (2 ^ (Cube.hstar a - 1)) ∧ Bd w (2 ^ (128 * L)) (kT x) env ∧
      a < 2 ^ L ∧ 3 * (Nat.log 2 a + 1) + 5 < 2 ^ L ∧ 2 ^ (Cube.hstar a - 1) < 2 ^ L ∧
      L < 2 ^ L ∧ Nat.log 2 a + 1 ≤ SqrtLog a ∧ 8 * (Nat.log 2 a + 1) ≤ L ∧
      (a + 2) * (a + 2) ≤ 2 ^ (128 * L) := by
  have h1 := one_le_of_log ha
  have hsl : Nat.log 2 a + 1 ≤ SqrtLog a := by
    have := log2_add_one_le_sqrtLog a; rwa [Nat.log2_eq_log_two] at this
  have hlL : 8 * (Nat.log 2 a + 1) ≤ L := hL ▸ Nat.mul_le_mul hc hsl
  have ha2 : a < 2 ^ (Nat.log 2 a + 1) := Nat.lt_pow_succ_log_self (by norm_num) a
  have haL : a < 2 ^ L := ha2.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hsq : (a + 2) * (a + 2) ≤ 2 ^ (128 * L) := by
    have : a + 2 ≤ 2 ^ (Nat.log 2 a + 2) := by rw [pow_succ]; omega
    calc (a + 2) * (a + 2) ≤ 2 ^ (Nat.log 2 a + 2) * 2 ^ (Nat.log 2 a + 2) :=
          Nat.mul_le_mul this this
      _ = 2 ^ (2 * Nat.log 2 a + 4) := by rw [← pow_add]; ring_nf
      _ ≤ 2 ^ (128 * L) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hLM : L ≤ 2 ^ (128 * L) :=
    (Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
  have h4a : 4 * a + 8 ≤ 2 ^ (128 * L) := by nlinarith
  have h2a : 2 * a + 2 ≤ 2 ^ (128 * L) := by omega
  exact ⟨hL ▸ val_bLT c hx h1, bd_bLT c hx hbx h1 hsq (hL ▸ hLM) (by omega),
    val_fwT hx h1, bd_fwT hx hbx h1 h4a, val_kT hx ha, bd_kT hx hbx ha h2a, haL,
    (by omega : 3 * (Nat.log 2 a + 1) + 5 ≤ L).trans_lt Nat.lt_two_pow_self,
    (kT_le ha).trans_lt haL, Nat.lt_two_pow_self, hsl, hlL, hsq⟩

/-- `E = (C + 1)(s + 2)^(C + 2) ≤ 2^((3C + 5)(⌊log₂ s⌋ + 1))`. -/
theorem expE_le (C s : ℕ) : CubeCounting.expE C s ≤ 2 ^ ((3 * C + 5) * (Nat.log 2 s + 1)) := by
  have hs : s < 2 ^ (Nat.log 2 s + 1) := Nat.lt_pow_succ_log_self (by norm_num) s
  have h2 : s + 2 ≤ 2 ^ (2 * (Nat.log 2 s + 1)) := by
    have : 2 ^ (Nat.log 2 s + 2) ≤ 2 ^ (2 * (Nat.log 2 s + 1)) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [pow_succ] at this; omega
  have h3 : C + 1 ≤ 2 ^ ((C + 1) * (Nat.log 2 s + 1)) :=
    (Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_right (by norm_num)
      (Nat.le_mul_of_pos_right _ (by omega)))
  calc CubeCounting.expE C s = (C + 1) * (s + 2) ^ (C + 2) := rfl
    _ ≤ 2 ^ ((C + 1) * (Nat.log 2 s + 1)) * (2 ^ (2 * (Nat.log 2 s + 1))) ^ (C + 2) :=
        Nat.mul_le_mul h3 (Nat.pow_le_pow_left h2 _)
    _ = 2 ^ ((3 * C + 5) * (Nat.log 2 s + 1)) := by rw [← pow_mul, ← pow_add]; ring_nf

/-! ### Calling the evaluator under a test -/

theorem denote_iteCall {c a : Term} {q : Prog} (hq : Prog'.closed 1 q = true) (env : List ℕ) :
    (ite c (call1 q a) (const 0)).denote w env =
      if 0 < c.denote w env then q.eval w [a.denote w env] else 0 := by
  change (Prog.ite (c env.length) (Prog.letIn (a env.length) q) (Prog.const 0)).eval w env = _
  simp only [Prog.eval]
  rw [show q.eval w ((a env.length).eval w env :: env) = q.eval w [(a env.length).eval w env] from
    Prog'.eval_append q [_] env hq]
  rfl

theorem bnd_iteCall {c a : Term} {q : Prog} (hq : Prog'.closed 1 q = true) {env : List ℕ}
    (hc : c.Bnd w M env)
    (ht : 0 < c.denote w env → a.Bnd w M env ∧ q.Bounded w M [a.denote w env]) :
    (ite c (call1 q a) (const 0)).Bnd w M env := by
  change Prog.Bounded w M (.ite (c env.length) (.letIn (a env.length) q) (.const 0)) env
  simp only [Prog.Bounded]
  refine ⟨hc, ?_⟩
  split_ifs with h
  · obtain ⟨h1, h2⟩ := ht h
    exact ⟨h1, (Prog'.bounded_append M q [_] env hq).mpr h2⟩
  · exact Nat.zero_le _

/-- The evaluator on the programs of the formula, closed over `[par]`. -/
def evalProg (T : Cube.Num.CubeT) : Prog := closeAt 1 (Cube.Num.formulaBitT T 1)

theorem eval_evalProg (T : Cube.Num.CubeT) (par : ℕ) :
    (evalProg T).eval w [par] = (Cube.Num.formulaBitT T).denote w [par] :=
  eval_closeAt _ 1 [par] rfl

theorem bounded_evalProg (T : Cube.Num.CubeT) (par : ℕ) :
    (evalProg T).Bounded w M [par] ↔ (Cube.Num.formulaBitT T).Bnd w M [par] :=
  bounded_closeAt _ 1 [par] rfl

/-! ### A logspace family -/

/-- The parameter `[s, P, B, fw, K, H]` of a logspace family over `[s, |w|, j]`, with `P = j + 1`
and `B = H = c · SqrtLog s`. -/
def famParT (c : ℕ) : Term :=
  Cube.Num.encE [lvl 2, add (lvl 0) (const 1), bLT c (lvl 2), fwT (lvl 2), kT
      (lvl 2), bLT c (lvl 2)]

/-- The term of Theorem 2.3 over `[s, |w|, j]`: `0` for `j ≥ E`, else the evaluator at the
parameter of the family. -/
def famTopT (F : LogspaceNetFamily) (c : ℕ) : Term :=
  ite (lt (lvl 0) (expT' F.C (lvl 2))) (call1 (evalProg (Cube.Num.famCubeT F))
      (famParT c)) (const 0)

/-- **The program of Theorem 2.3**, closed over `[s, |w|, j]`. -/
def famProg (F : LogspaceNetFamily) (c : ℕ) : Prog := closeAt 3 (famTopT F c 3)

theorem abs_eval_le (F : LogspaceNetFamily) {w : List Bool} {s : ℕ} (hm : F.Mem w s) {C₁ : ℕ}
    (hC : F.C ≤ C₁) (v : Fin (F.V w s)) (l : List Bool)
    (hl : l.length = ((F.net w s).ports v).length) :
    |(F.net w s).eval v l| ≤ ((s + 2) ^ C₁ : ℕ) := by
  obtain ⟨h0, h1⟩ := F.eval_mem w s hm v l hl
  rw [abs_of_nonneg h0]
  refine h1.trans ?_
  have : (s + 2) ^ F.C ≤ (s + 2) ^ C₁ := Nat.pow_le_pow_right (by omega) hC
  exact_mod_cast this

end CubeFinal

open CubeFinal

/-- **Theorem 2.3 in bit form** (`thm:counting`): for every family of networks with logspace
access, one closed program over `[s, |w|, j]` computes bit `j` of `Z(G)`, with every value of its
evaluation below `2^(C · SqrtLog s)`. -/
theorem cubeCounting : CubeCounting := by
  intro F
  obtain ⟨c₀, s₀, hcore⟩ := Cube.Num.cube_bit_size (3 * F.C + 5) (by omega)
  refine ⟨famProg F (c₀ + 5 * F.C + 16), 128 * (c₀ + 5 * F.C + 16), s₀ + 256, closed_closeAt _ _,
    fun w s j hm hs => ?_⟩
  generalize hc : c₀ + 5 * F.C + 16 = c
  obtain ⟨L, hL⟩ : ∃ L, L = c * SqrtLog s := ⟨_, rfl⟩
  rw [show 128 * c * SqrtLog s = 128 * L by rw [hL, mul_assoc]]
  have hs8 : 3 ≤ Nat.log 2 s := Nat.le_log_of_pow_le (by norm_num) (by omega)
  have hs1 := one_le_of_log hs8
  have vs : Val w (lvl 2) [s, w.length, j] s := val_lvl (by simp)
  have vj : Val w (lvl 0) [s, w.length, j] j := val_lvl (by simp)
  obtain ⟨vB, bB, vfw, bfw, vK, bK, hsL, hfwL, hKL, hLL, hsl, hlL, hsq⟩ :=
    size_terms vs (bd_lvl _ _) hs8 (by omega : 8 ≤ c) hL
  have hE := expE_le F.C s
  have hℓL : (3 * F.C + 5) * (Nat.log 2 s + 1) < L := by
    have : (3 * F.C + 5) * (Nat.log 2 s + 1) < c * (Nat.log 2 s + 1) :=
      Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
    exact this.trans_le (hL ▸ Nat.mul_le_mul_left _ hsl)
  have hEL : CubeCounting.expE F.C s < 2 ^ L :=
    hE.trans_lt (Nat.pow_lt_pow_right (by norm_num) hℓL)
  have hLM : 2 ^ (L + 1) ≤ 2 ^ (128 * L) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have vE := val_expT' F.C vs
  have bE : Bd w (2 ^ (128 * L)) (expT' F.C (lvl 2)) [s, w.length, j] := by
    refine bd_expT' F.C vs (bd_lvl _ _) ?_
    have : (F.C + 2) * (s + 2) ^ (F.C + 2) ≤ 2 * CubeCounting.expE F.C s :=
      calc (F.C + 2) * (s + 2) ^ (F.C + 2) ≤ (2 * (F.C + 1)) * (s + 2) ^ (F.C + 2) :=
            Nat.mul_le_mul_right _ (by omega)
        _ = 2 * CubeCounting.expE F.C s := by unfold CubeCounting.expE; ring
    rw [pow_succ] at hLM; omega
  have vc := val_lt vj vE
  have hq : Prog'.closed 1 (evalProg (Cube.Num.famCubeT F)) = true := closed_closeAt _ _
  -- the parameter and the evaluator, below `E`
  have key : j < CubeCounting.expE F.C s →
      (famParT c).denote w [s, w.length, j] =
          Cube.Num.famPar s (j + 1) L (3 * (Nat.log 2 s + 1) + 5) (2 ^ (Cube.hstar s - 1)) L ∧
        (famParT c).Bnd w (2 ^ (128 * L)) [s, w.length, j] ∧
        (Cube.Num.formulaBitT (Cube.Num.famCubeT F)).denote w
            [Cube.Num.famPar s (j + 1) L (3 * (Nat.log 2 s + 1) + 5) (2 ^ (Cube.hstar s - 1)) L] =
          (F.net w s).value.toNat / 2 ^ j % 2 ∧
        (Cube.Num.formulaBitT (Cube.Num.famCubeT F)).Bnd w (2 ^ (128 * L))
          [Cube.Num.famPar s (j + 1) L (3 * (Nat.log 2 s + 1) + 5) (2 ^ (Cube.hstar s - 1)) L] := by
    intro hj
    have hPL : j + 1 < 2 ^ L := by omega
    have vP : Val w (add (lvl 0) (const 1)) [s, w.length, j] (j + 1) := val_add vj (val_const 1 _)
    have bP : Bd w (2 ^ (128 * L)) (add (lvl 0) (const 1)) [s, w.length, j] :=
      bd_add (bd_lvl _ _) (bd_const (by rw [pow_succ] at hLM; omega) _) vj (val_const 1 _)
        (by rw [pow_succ] at hLM; omega)
    have hfields : ∀ x ∈ [s, j + 1, L, 3 * (Nat.log 2 s + 1) + 5, 2 ^ (Cube.hstar s - 1), L],
        x < 2 ^ L := by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro x (rfl | rfl | rfl | rfl | rfl | rfl) <;> assumption
    have vpar := Cube.Num.val_encE (w := w) (env := [s, w.length, j])
      (.cons (numVal vs) (.cons (numVal vP) (.cons (numVal vB) (.cons (numVal vfw)
        (.cons (numVal vK) (.cons (numVal vB) .nil))))))
    have henc : NatList.enc [s, j + 1, L, 3 * (Nat.log 2 s + 1) + 5, 2 ^ (Cube.hstar s - 1), L] <
        2 ^ (29 * L) := (Cube.enc_lt_of_mem (by simp) hfields).trans_le
          (Nat.pow_le_pow_right (by norm_num) (by omega))
    have tpar : Tm w L 29 (famParT c) [s, w.length, j] :=
      Cube.Num.tm_encE (by norm_num) le_rfl (by omega)
        (.cons ⟨numVal vs, 1, tm_of (bd_lvl _ _) vs hsL⟩ (.cons ⟨numVal vP, 1, tm_of bP vP hPL⟩
          (.cons ⟨numVal vB, 1, tm_of bB vB hLL⟩ (.cons ⟨numVal vfw, 1, tm_of bfw vfw hfwL⟩
            (.cons ⟨numVal vK, 1, tm_of bK vK hKL⟩ (.cons ⟨numVal vB, 1, tm_of bB vB hLL⟩ .nil))))))
        henc
    have hCF : F.C ≤ 3 * F.C + 5 := by omega
    have hlog : (2 * F.C + 3) * (s.log2 + 1) ≤ L := by
      rw [Nat.log2_eq_log_two]
      exact (Nat.mul_le_mul_right _ (by omega : 2 * F.C + 3 ≤ c)).trans
          (hL ▸ Nat.mul_le_mul_left _ hsl)
    obtain ⟨hN, tP, tB, tfw, tK, tH⟩ := Cube.Num.famCube_tiers hm hfields (by omega) hlog
    have hc₀ : c₀ * SqrtLog s ≤ L := hL ▸ Nat.mul_le_mul_right _ (by omega)
    obtain ⟨hv, hb⟩ := hcore s (by omega) L hc₀ (F.net w s) (j + 1)
      ((F.verts_le w s hm).trans (Nat.pow_le_pow_right (by omega) hCF))
      ((F.edges_le w s hm).trans (Nat.mul_le_mul_right _ hCF))
      (fun v => (F.deg_le w s hm v).trans (Nat.mul_le_mul_right _ hCF))
      (fun v l hl => abs_eval_le F hm hCF v l hl) (fun v l hl => (F.eval_mem w s hm v l hl).1)
      (by omega) (by omega) (Cube.Num.famCube_in hm) hN tP tB tfw tK tH
    rw [Nat.add_sub_cancel] at hv
    exact ⟨vpar.2, tpar.bnd, hv, hb⟩
  have e1 : (famProg F c).eval w [s, w.length, j] = (famTopT F c).denote w [s, w.length, j] :=
    eval_closeAt _ 3 _ rfl
  have e2 : (famProg F c).Bounded w (2 ^ (128 * L)) [s, w.length, j] ↔
      (famTopT F c).Bnd w (2 ^ (128 * L)) [s, w.length, j] := bounded_closeAt _ 3 _ rfl
  rw [e1, e2]
  refine ⟨?_, bnd_iteCall hq (bd_lt (bd_lvl _ _) bE).bnd fun h => ?_⟩
  rotate_left
  · rw [vc.eq] at h
    have hj : j < CubeCounting.expE F.C s := by
      by_contra hj; rw [ite_eq_right hj] at h; exact Nat.lt_irrefl 0 h
    obtain ⟨k1, k2, -, k4⟩ := key hj
    rw [k1, bounded_evalProg]
    exact ⟨k2, k4⟩
  rw [famTopT, denote_iteCall hq, vc.eq]
  by_cases hj : j < CubeCounting.expE F.C s
  · rw [ite_eq_left (by simp [hj] : 0 < (if j < CubeCounting.expE F.C s then 1 else 0))]
    obtain ⟨k1, -, k3, -⟩ := key hj
    rw [k1, eval_evalProg, k3]
  · rw [ite_eq_right (by simp [hj] : ¬ 0 < (if j < CubeCounting.expE F.C s then 1 else 0))]
    have hv := CubeCounting.toNat_value_lt F hm
    have : (F.net w s).value.toNat < 2 ^ j :=
      hv.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [Nat.div_eq_of_lt this]

/-! ### The block networks -/

namespace CubeFinal

open _root_.Turing Cslib.Complexity Cslib.Complexity.CountingSimulation Finset

section Block

variable {k s : ℕ} {State : Type} [DecidableEq State] {machine : MultiTapePTM k Bool State}
  {e : State ≃ Fin s}

omit [DecidableEq State] in
/-- The vertex functions of a block network are at most `2^(blockLength τ) ≤ 2(τ + 2)`. -/
theorem blockNet_eval_le {w : List Bool} {τ σ : ℕ} (hd : NetTerm.RowsFirst machine e w τ σ)
    (v : Fin (blockNetworkOf machine e (w, τ, σ)).2.vertices.length) (l : List Bool)
    (hl : l.length = ((Cube.Num.blockNet machine e w τ σ hd).ports v).length) :
    |(Cube.Num.blockNet machine e w τ σ hd).eval v l| ≤ 2 * (τ + 2) := by
  classical
  have h1 := NetTerm.denote_evalAtT_bits (machine := machine) (e := e) (nT := const w.length)
    (τT := const τ) (σT := const σ) (env := []) (t := τ) (σ := σ) (p := 0)
    (stableAt_const _ _) rfl (stableAt_const _ _) rfl (stableAt_const _ _) rfl hd
    (pT := const 0) (vT := const v) (AT := const (Cslib.BitString.lsbValue l)) rfl
    (stableAt_const _ _) (v := v) rfl (stableAt_const _ _) hl rfl
  have h2 : (NetTerm.evalAtT k s machine e (const w.length) (const τ) (const σ) (const 0) (const v)
      (const (Cslib.BitString.lsbValue l))).denote w [] ≤ 2 ^ blockLength τ := by
    rw [NetTerm.evalAtT, denote_mod, denote_const, Nat.mod_zero, NetTerm.clkWeightT]
    refine (LocalSim.weightNT_le _ _ _ _ _ _ _ _).trans_eq ?_
    rw [NetTerm.denote_clkBlockLenT (stableAt_const _ _) rfl, denote_const]
  have h3 := Cube.Num.blockNet_eval_toNat hd v l
  have h4 := Cube.Num.blockNet_evalNonneg hd v l hl
  rw [abs_of_nonneg h4, ← Int.toNat_of_nonneg h4, h3, ← h1]
  exact_mod_cast h2.trans (two_pow_blockLength_le τ)

/-- `numBlocks τ ≤ SqrtLog τ + 1`. -/
theorem numBlocks_le {τ : ℕ} (hτ : 2 ≤ τ) : numBlocks τ ≤ SqrtLog τ + 1 := by
  have hbl : Nat.log 2 τ + 1 ≤ blockLength τ := by
    rw [blockLength, clog_eq_log_add_one]
    exact Nat.add_le_add_right (Nat.log_mono_right (by omega)) 1
  have hb1 : 1 ≤ blockLength τ := by omega
  rw [numBlocks, Nat.ceilDiv_eq_add_pred_div]
  calc (τ + blockLength τ - 1) / blockLength τ ≤ (τ + blockLength τ) / blockLength τ :=
        Nat.div_le_div_right (by omega)
    _ = τ / blockLength τ + 1 := Nat.add_div_right _ (by omega)
    _ ≤ τ / (Nat.log 2 τ + 1) + 1 := Nat.add_le_add_right (Nat.div_le_div_left hbl (by omega)) 1
    _ ≤ SqrtLog τ + 1 := Nat.add_le_add_right (div_log_le_sqrtLog' hτ) 1

omit [DecidableEq State] in
/-- The contraction of a block network is below `2^(2τ)`. -/
theorem contraction_lt [Finite State] (w : List Bool) {τ σ : ℕ} (hτ : 2 ≤ τ)
    (hσ : σ < scheduleCount (k + 1) τ) :
    (blockNetworkOf machine e (w, τ, σ)).2.contraction < 2 ^ (2 * τ) := by
  have hA := sum_contraction_blockNetworkOf machine e w hτ
  have hAle : machine.acceptCount w (paddedTime τ) ≤ 2 ^ paddedTime τ := acceptCount_le_two_pow
  have hT1 : paddedTime τ + 1 ≤ 2 * τ := paddedTime_add_one_le hτ
  have h1 : (blockNetworkOf machine e (w, τ, σ)).2.contraction ≤
      ∑ σ ∈ range (scheduleCount (k + 1) τ), (blockNetworkOf machine e (w, τ, σ)).2.contraction :=
    single_le_sum (f := fun σ => (blockNetworkOf machine e (w, τ, σ)).2.contraction)
      (fun _ _ => Nat.zero_le _) (mem_range.mpr hσ)
  have h2 : 2 ^ paddedTime τ < 2 ^ (2 * τ) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

/-- `c · t ≤ (t + 2)^(c + 2)`. -/
theorem mul_le_pow (c t : ℕ) : c * t ≤ (t + 2) ^ (c + 2) := by
  have h1 : c ≤ (t + 2) ^ c :=
    (Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_left (by omega) c)
  have h2 : t ≤ (t + 2) ^ 2 := by nlinarith
  calc c * t ≤ (t + 2) ^ c * (t + 2) ^ 2 := Nat.mul_le_mul h1 h2
    _ = (t + 2) ^ (c + 2) := by rw [← pow_add]

end Block

variable {k s : ℕ} {State : Type} [DecidableEq State] (machine : MultiTapePTM k Bool State)
  (e : State ≃ Fin s)

/-- The parameter `[n, τ, σ, P, B, fw, K, H]` of the block networks over `[τ, |w|, σ, j]`, with
`P = j + 1` and `B = H = c · SqrtLog τ`. -/
def blockParT (c : ℕ) : Term :=
  Cube.Num.encE [lvl 2, lvl 3, lvl 1, add (lvl 0) (const 1), bLT c (lvl 3), fwT (lvl 3), kT (lvl 3),
    bLT c (lvl 3)]

/-- The term of the bits of the block networks over `[τ, |w|, σ, j]`: `0` for `j ≥ 2τ`, else the
evaluator at the parameter of the block network. -/
def blockTopT (c : ℕ) : Term :=
  ite (lt (lvl 0) (mul (const 2) (lvl 3))) (call1 (evalProg (Cube.Num.blockCubeT machine e))
    (blockParT c)) (const 0)

/-- **The program of the bits of the block networks**, closed over `[τ, |w|, σ, j]`. -/
def blockProg (c : ℕ) : Prog := closeAt 4 (blockTopT machine e c 4)

end CubeFinal

open Cslib.Complexity.CountingSimulation in
/-- **The bits of the block networks** (Theorem 2.3 for the networks of Lemma 2.2): one closed
program over `[τ, |w|, σ, j]` computes bit `j` of the contraction of the block network of schedule
`σ` at clock `τ`, with every value below `2^(C · SqrtLog τ)`. -/
theorem cubeBlockBits : Exact.BlockBits := by
  intro k State _ _ machine s e
  obtain ⟨c₀, s₀, hcore⟩ := Cube.Num.cube_bit_size (6 * (3 * k + 1) * (s + k + 4) + 2) (by omega)
  refine ⟨blockProg machine e (c₀ + Cube.Num.blockBudget k s + 4 * k + 12),
    128 * (c₀ + Cube.Num.blockBudget k s + 4 * k + 12), s₀ + 256, closed_closeAt _ _,
    fun w τ σ j hwτ hτ hσ => ?_⟩
  generalize hc : c₀ + Cube.Num.blockBudget k s + 4 * k + 12 = c
  generalize hCb : 6 * (3 * k + 1) * (s + k + 4) = Cb at hcore
  obtain ⟨L, hL⟩ : ∃ L, L = c * SqrtLog τ := ⟨_, rfl⟩
  rw [show 128 * c * SqrtLog τ = 128 * L by rw [hL, mul_assoc]]
  have hτ8 : 3 ≤ Nat.log 2 τ := Nat.le_log_of_pow_le (by norm_num) (by omega)
  have hτ2 : 2 ≤ τ := by omega
  have vτ : Val w (lvl 3) [τ, w.length, σ, j] τ := val_lvl (by simp)
  have vn : Val w (lvl 2) [τ, w.length, σ, j] w.length := val_lvl (by simp)
  have vσ : Val w (lvl 1) [τ, w.length, σ, j] σ := val_lvl (by simp)
  have vj : Val w (lvl 0) [τ, w.length, σ, j] j := val_lvl (by simp)
  obtain ⟨vB, bB, vfw, bfw, vK, bK, hτL, hfwL, hKL, hLL, hsl, hlL, hsq⟩ :=
    size_terms vτ (bd_lvl _ _) hτ8 (by omega : 8 ≤ c) hL
  have hLM : 2 ^ (L + 1) ≤ 2 ^ (128 * L) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2L : 2 ^ (L + 1) = 2 * 2 ^ L := by rw [pow_succ]; ring
  have vE : Val w (mul (const 2) (lvl 3)) [τ, w.length, σ, j] (2 * τ) := val_mul (val_const 2 _) vτ
  have bE : Bd w (2 ^ (128 * L)) (mul (const 2) (lvl 3)) [τ, w.length, σ, j] :=
    bd_mul (bd_const (by omega) _) (bd_lvl _ _) (val_const 2 _) vτ (by omega)
  have vc := val_lt vj vE
  have hq : Prog'.closed 1 (evalProg (Cube.Num.blockCubeT machine e)) = true := closed_closeAt _ _
  have hd := Cube.Num.rowsFirst_of_two_le machine e w σ hτ2
  have hadm := explicitAdmissible_blockNetworkOf machine e w σ hτ2
  rw [hCb] at hadm
  -- the parameter and the evaluator, below `2τ`
  have key : j < 2 * τ →
      (blockParT c).denote w [τ, w.length, σ, j] = Cube.Num.blockPar w.length τ σ (j + 1) L
          (3 * (Nat.log 2 τ + 1) + 5) (2 ^ (Cube.hstar τ - 1)) L ∧
        (blockParT c).Bnd w (2 ^ (128 * L)) [τ, w.length, σ, j] ∧
        (Cube.Num.formulaBitT (Cube.Num.blockCubeT machine e)).denote w
            [Cube.Num.blockPar w.length τ σ (j + 1) L (3 * (Nat.log 2 τ + 1) + 5)
              (2 ^ (Cube.hstar τ - 1)) L] =
          (blockNetworkOf machine e (w, τ, σ)).2.contraction / 2 ^ j % 2 ∧
        (Cube.Num.formulaBitT (Cube.Num.blockCubeT machine e)).Bnd w (2 ^ (128 * L))
          [Cube.Num.blockPar w.length τ σ (j + 1) L (3 * (Nat.log 2 τ + 1) + 5)
            (2 ^ (Cube.hstar τ - 1)) L] := by
    intro hj
    have hτl : τ < 2 ^ (Nat.log 2 τ + 1) := Nat.lt_pow_succ_log_self (by norm_num) τ
    have h2τ : 2 * τ ≤ 2 ^ (2 * (Nat.log 2 τ + 1)) := by
      have : 2 ^ (Nat.log 2 τ + 2) ≤ 2 ^ (2 * (Nat.log 2 τ + 1)) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [pow_succ] at this; omega
    have h2τL : 2 * τ ≤ 2 ^ L := h2τ.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
    have hPL : j + 1 < 2 ^ L := by
      have : 2 ^ (2 * (Nat.log 2 τ + 1)) < 2 ^ L := Nat.pow_lt_pow_right (by norm_num) (by omega)
      omega
    have vP : Val w (add (lvl 0) (const 1)) [τ, w.length, σ, j] (j + 1) :=
      val_add vj (val_const 1 _)
    have bP : Bd w (2 ^ (128 * L)) (add (lvl 0) (const 1)) [τ, w.length, σ, j] :=
      bd_add (bd_lvl _ _) (bd_const (by omega) _) vj (val_const 1 _) (by omega)
    have hnL : w.length < 2 ^ L := lt_of_le_of_lt hwτ hτL
    have hσL : σ < 2 ^ L := by
      have h1 : scheduleCount (k + 1) τ ≤ 2 ^ (2 * ((k + 1) * numBlocks τ)) := Cube.Num.pow3_le' _
      have h2 : 2 * ((k + 1) * numBlocks τ) ≤ L := by
        have hnb := numBlocks_le hτ2
        have hS1 : 1 ≤ SqrtLog τ := Nat.le_add_left _ _
        calc 2 * ((k + 1) * numBlocks τ) ≤ 2 * ((k + 1) * (SqrtLog τ + 1)) :=
              Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hnb)
          _ ≤ 2 * ((k + 1) * (2 * SqrtLog τ)) :=
              Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
          _ = (4 * k + 4) * SqrtLog τ := by ring
          _ ≤ c * SqrtLog τ := Nat.mul_le_mul_right _ (by omega)
          _ = L := hL.symm
      exact (hσ.trans_le h1).trans_le (Nat.pow_le_pow_right (by norm_num) h2)
    have hfields : ∀ x ∈ [w.length, τ, σ, j + 1, L, 3 * (Nat.log 2 τ + 1) + 5,
        2 ^ (Cube.hstar τ - 1), L], x < 2 ^ L := by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro x (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> assumption
    have vpar := Cube.Num.val_encE (w := w) (env := [τ, w.length, σ, j])
      (.cons (numVal vn) (.cons (numVal vτ) (.cons (numVal vσ) (.cons (numVal vP)
        (.cons (numVal vB) (.cons (numVal vfw) (.cons (numVal vK) (.cons (numVal vB) .nil))))))))
    have henc : NatList.enc [w.length, τ, σ, j + 1, L, 3 * (Nat.log 2 τ + 1) + 5,
        2 ^ (Cube.hstar τ - 1), L] < 2 ^ (29 * L) :=
      (Cube.enc_lt_of_mem (by simp) hfields).trans_le
        (Nat.pow_le_pow_right (by norm_num) (by omega))
    have tpar : Tm w L 29 (blockParT c) [τ, w.length, σ, j] :=
      Cube.Num.tm_encE (by norm_num) le_rfl (by omega)
        (.cons ⟨numVal vn, 1, tm_of (bd_lvl _ _) vn hnL⟩
          (.cons ⟨numVal vτ, 1, tm_of (bd_lvl _ _) vτ hτL⟩
            (.cons ⟨numVal vσ, 1, tm_of (bd_lvl _ _) vσ hσL⟩
              (.cons ⟨numVal vP, 1, tm_of bP vP hPL⟩ (.cons ⟨numVal vB, 1, tm_of bB vB hLL⟩
                (.cons ⟨numVal vfw, 1, tm_of bfw vfw hfwL⟩ (.cons ⟨numVal vK, 1, tm_of bK vK hKL⟩
                  (.cons ⟨numVal vB, 1, tm_of bB vB hLL⟩ .nil))))))))
        henc
    have hbb : Cube.Num.blockBudget k s * (τ.log2 + 1) ≤ L := by
      rw [Nat.log2_eq_log_two]
      exact (Nat.mul_le_mul_right _ (by omega : Cube.Num.blockBudget k s ≤ c)).trans
        (hL ▸ Nat.mul_le_mul_left _ hsl)
    obtain ⟨hN, tP, tB, tfw, tK, tH⟩ := Cube.Num.blockCube_tiers hd hτ2 hwτ hfields (by omega) hbb
    have hc₀ : c₀ * SqrtLog τ ≤ L := hL ▸ Nat.mul_le_mul_right _ (by omega)
    have hV : (blockNetworkOf machine e (w, τ, σ)).2.vertices.length ≤ (τ + 2) ^ (Cb + 2) :=
      hadm.2.2.2.1.trans (mul_le_pow Cb τ)
    have hM : (Cube.Num.blockNet machine e w τ σ hd).M ≤ (Cb + 2) * (τ + 1) := by
      rw [Cube.Num.blockNet_M hd]
      refine (Cube.Num.edgesN_le_mul' hτ2).trans ?_
      rw [← hCb]
      calc 4 * (3 * k + 1) * (s + k + 4) * τ ≤ 6 * (3 * k + 1) * (s + k + 4) * τ :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by norm_num)))
        _ ≤ 6 * (3 * k + 1) * (s + k + 4) * τ + (6 * (3 * k + 1) * (s + k + 4) + 2 * τ + 2) :=
            Nat.le_add_right _ _
        _ = (6 * (3 * k + 1) * (s + k + 4) + 2) * (τ + 1) := by ring
    have hdeg : ∀ v, ((Cube.Num.blockNet machine e w τ σ hd).ports v).length ≤
        (Cb + 2) * (Nat.log 2 τ + 1) := fun v =>
      (NetTerm.length_ports_le (p := 0) hd hadm v).trans
        (Nat.mul_le_mul (by omega) (by omega))
    have hev : ∀ v l, l.length = ((Cube.Num.blockNet machine e w τ σ hd).ports v).length →
        |(Cube.Num.blockNet machine e w τ σ hd).eval v l| ≤ (((τ + 2) ^ (Cb + 2) : ℕ) : ℤ) := by
      intro v l hl
      refine (blockNet_eval_le hd v l hl).trans ?_
      have : 2 * (τ + 2) ≤ (τ + 2) ^ (Cb + 2) :=
        calc 2 * (τ + 2) ≤ (τ + 2) * (τ + 2) := Nat.mul_le_mul_right _ (by omega)
          _ = (τ + 2) ^ 2 := (sq _).symm
          _ ≤ (τ + 2) ^ (Cb + 2) := Nat.pow_le_pow_right (by omega) (by omega)
      exact_mod_cast this
    have hPℓ : j + 1 ≤ 2 ^ ((Cb + 2) * (Nat.log 2 τ + 1)) :=
      (show j + 1 ≤ 2 * τ by omega).trans (h2τ.trans (Nat.pow_le_pow_right (by norm_num)
        (Nat.mul_le_mul_right _ (by omega))))
    obtain ⟨hv, hb⟩ := hcore τ (by omega) L hc₀ (Cube.Num.blockNet machine e w τ σ hd) (j + 1)
      hV hM hdeg hev (Cube.Num.blockNet_evalNonneg hd) (by omega) hPℓ (Cube.Num.blockCube_in hd)
      hN tP tB tfw tK tH
    rw [Nat.add_sub_cancel, Cube.Num.blockNet_value hd, Int.toNat_natCast] at hv
    exact ⟨vpar.2, tpar.bnd, hv, hb⟩
  have e1 : (blockProg machine e c).eval w [τ, w.length, σ, j] =
      (blockTopT machine e c).denote w [τ, w.length, σ, j] := eval_closeAt _ 4 _ rfl
  have e2 : (blockProg machine e c).Bounded w (2 ^ (128 * L)) [τ, w.length, σ, j] ↔
      (blockTopT machine e c).Bnd w (2 ^ (128 * L)) [τ, w.length, σ, j] :=
    bounded_closeAt _ 4 _ rfl
  rw [e1, e2]
  refine ⟨?_, bnd_iteCall hq (bd_lt (bd_lvl _ _) bE).bnd fun h => ?_⟩
  rotate_left
  · rw [vc.eq] at h
    have hj : j < 2 * τ := by
      by_contra hj; rw [ite_eq_right hj] at h; exact Nat.lt_irrefl 0 h
    obtain ⟨k1, k2, -, k4⟩ := key hj
    rw [k1, bounded_evalProg]
    exact ⟨k2, k4⟩
  rw [blockTopT, denote_iteCall hq, vc.eq]
  by_cases hj : j < 2 * τ
  · rw [ite_eq_left (by simp [hj] : 0 < (if j < 2 * τ then 1 else 0))]
    obtain ⟨k1, -, k3, -⟩ := key hj
    rw [k1, eval_evalProg, k3]
  · rw [ite_eq_right (by simp [hj] : ¬ 0 < (if j < 2 * τ then 1 else 0))]
    have : (blockNetworkOf machine e (w, τ, σ)).2.contraction < 2 ^ j :=
      (contraction_lt w hτ2 hσ).trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [Nat.div_eq_of_lt this]

end Cslib.Complexity.NtimeDspace.Cross
