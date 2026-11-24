/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.CubeStatement
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.ThreeSatFinal

/-!
# Theorem 2.3 in bit form, and the residues it gives

The paper's Theorem 2.3 (`thm:counting`): for a family of networks with logspace access at size
`s`, given `s` and the description of a network `G` of the family, every bit of `Z(G)` is computed
in space `O(s/√log s)` and time `2^{O(s/√log s)}`. `CubeCounting` states it in the program model
of `LogspaceNetFamily`: one closed program on `[s, |w|, j]` computes bit `j` of `Z(G)` for every
`j`, with every value of its evaluation at most `2^(C · SqrtLog s)`. The bit position `j` is an
input variable, and `Prog.Bounded` bounds only the values computed, not the environment, so the
bound can hold for every `j`. The vertex functions of the family take values in
`{0, …, (s+2)^C}`, so `Z(G) ≥ 0` (`value_nonneg`) and bit `j` of `Z(G)` is the bit of the natural
number `Z(G).toNat`. The statement and these bounds are in `CubeStatement.lean`; the proof is
`cubeCounting` of `CubeFinal.lean`.

From the bits, `residueProg` computes `Z(G) mod p` for every prime `p ≤ s`: since
`Z(G) < 2^E` for `E = (C + 1)(s + 2)^(C + 2)` (`toNat_value_lt`), it accumulates
`Σ_{k<E} bit_k(Z) · (2^k mod p)` modulo `p`, with every value at most a polynomial in `s` besides
the values of the bit program. This is the residue form `ThreeSat.Theorem41` of Theorem 2.3 that
`ThreeSatFinal.lean` uses for Corollary 7.2, with the window exponent `c = 0` (every prime
`p ≤ s`), so Corollary 7.2 follows from `CubeCounting`.

## Main definitions

* `residueProg`: the residue program built from a bit program.

## Main results

* `theorem41_of_cubeCounting`: `CubeCounting` gives `ThreeSat.Theorem41`.
* `cor_3sat_of_cubeCounting`, `cor_3sat_bits_of_cubeCounting`: Corollary 7.2 (paper `cor:3sat`)
  from `CubeCounting`, in the forms `ThreeSat.cor_9_4` and `ThreeSat.cor_9_4_bits`.

## References

* The paper (`separating-ntime-from-space.tex`), §2, Definition 2.1 (`def:access`) and Theorem 2.3
(`thm:counting`);
  §7, Corollary 7.2 (`cor:3sat`).
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Cross

open NtimeDspace.ProgLang NtimeDspace.ProgTerm Term NtimeDspace.Cross.Exact Finset
  NtimeDspace.SumProduct

namespace CubeCounting

/-! ### Arithmetic of the residue loop -/

theorem foldl_pow2 {P : ℕ} (hP : 2 ≤ P) (k : ℕ) :
    (List.range k).foldl (fun a _ => a * 2 % P) 1 = 2 ^ k % P := by
  induction k with
  | zero => simp [Nat.mod_eq_of_lt (by omega : 1 < P)]
  | succ k ih => rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih,
      Nat.mod_mul_mod, pow_succ]

theorem foldl_residue {P : ℕ} (b : ℕ → ℕ) (N : ℕ) :
    (List.range N).foldl (fun a k => (a + b k * (2 ^ k % P)) % P) 0 =
      (∑ k ∈ range N, b k * 2 ^ k) % P := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih, sum_range_succ]
    exact (Nat.mod_modEq _ P).add ((Nat.mod_modEq _ P).mul_left _)

theorem sum_bits (Z N : ℕ) : ∑ k ∈ range N, Z / 2 ^ k % 2 * 2 ^ k = Z % 2 ^ N := by
  induction N with
  | zero => simp [Nat.mod_one]
  | succ N ih => rw [sum_range_succ, ih, pow_succ, Nat.mod_mul]; ring

/-! ### The residue program -/

variable {w : List Bool} {M : ℕ}

/-- `2^k mod p`, by doubling modulo `p`. -/
def pow2ModT (k p : Term) : Term := foldT k (const 1) fun acc _ => mod (mul acc (const 2)) p

theorem val_pow2ModT {env : List ℕ} {k p : Term} {K P : ℕ} (hk : Val w k env K)
    (hp : Val w p env P) (hP : 2 ≤ P) : Val w (pow2ModT k p) env (2 ^ K % P) := by
  have := val_foldT (f := fun acc _ => mod (mul acc (const 2)) p) hk (val_const 1 env)
    (fun a _ => a * 2 % P)
    fun pre u u' a q hu _ => val_mod (val_mul hu (val_const 2 _)) (hp.ext pre)
  rwa [foldl_pow2 hP] at this

theorem bd_pow2ModT {env : List ℕ} {k p : Term} {K P : ℕ} (hk : Val w k env K)
    (hp : Val w p env P) (hP : 2 ≤ P) (hbk : Bd w M k env) (hbp : Bd w M p env) (hK : K ≤ M)
    (hPM : 2 * P ≤ M) : Bd w M (pow2ModT k p) env := by
  refine bd_foldT (f := fun acc _ => mod (mul acc (const 2)) p) hk (val_const 1 env)
    (fun a _ => a * 2 % P)
    (fun pre u u' a q hu _ => val_mod (val_mul hu (val_const 2 _)) (hp.ext pre))
    hbk (bd_const (by omega) _) hK fun pre u u' a q _ ha hu _ hbu _ => ?_
  rw [foldl_pow2 hP] at ha
  have : a < P := ha ▸ Nat.mod_lt _ (by omega)
  exact bd_mod (bd_mul hbu (bd_const (by omega) _) hu (val_const 2 _) (by omega)) (hbp.ext pre)

/-- The exponent `E = (C + 1)(s + 2)^(C + 2)`, from a term for `s`. -/
def expT (C : ℕ) (s : Term) : Term :=
  mul (const (C + 1)) (ThreeSat.powC (add s (const 2)) (C + 2))

/-- The residue `Z mod p` on `[s, |w|, p]`, from a bit program `Q` on `[s, |w|, j]`:
`Σ_{k<E} Q(s, |w|, k) · (2^k mod p)`, reduced modulo `p` after every step. -/
def residueT (Q : Prog) (C : ℕ) : Term :=
  foldT (expT C (lvl 2)) (const 0) fun acc k =>
    mod (add acc (mul (call3 Q (lvl 2) (lvl 1) k) (pow2ModT k (lvl 0)))) (lvl 0)

/-- The residue program, closed over `[s, |w|, p]`. -/
def residueProg (Q : Prog) (C : ℕ) : Prog := closeAt 3 (residueT Q C 3)

section Residue

variable {Q : Prog} (hQ : Prog'.closed 3 Q = true) (C : ℕ) {s n P : ℕ}
include hQ

theorem val_residueT (hP : 2 ≤ P) :
    Val w (residueT Q C) [s, n, P]
      ((∑ k ∈ range (expE C s), Q.eval w [s, n, k] * 2 ^ k) % P) := by
  have hs : Val w (add (lvl 2) (const 2)) [s, n, P] (s + 2) :=
    val_add (ThreeSat.val_x3 s n) (val_const 2 _)
  have hE : Val w (expT C (lvl 2)) [s, n, P] (expE C s) :=
    val_mul (val_const _ _) (ThreeSat.val_powC (C + 2) hs)
  have := val_foldT (f := fun acc k =>
      mod (add acc (mul (call3 Q (lvl 2) (lvl 1) k) (pow2ModT k (lvl 0)))) (lvl 0))
    hE (val_const 0 _) (fun a k => (a + Q.eval w [s, n, k] * (2 ^ k % P)) % P)
    fun pre u u' a q hu hu' => val_mod (val_add hu (val_mul
      (val_call3 hQ ((ThreeSat.val_x3 s n).ext pre) ((ThreeSat.val_y3 s n).ext pre) hu')
      (val_pow2ModT hu' ((ThreeSat.val_s3 s n).ext pre) hP))) ((ThreeSat.val_s3 s n).ext pre)
  rwa [foldl_residue] at this

theorem bd_residueT (hP : 2 ≤ P) (hPs : P ≤ s) (hY : 2 * (C + 2) * (s + 2) ^ (C + 2) ≤ M)
    (hb : ∀ k, Q.eval w [s, n, k] ≤ 1) (hQb : ∀ k, Q.Bounded w M [s, n, k]) :
    Bd w M (residueT Q C) [s, n, P] := by
  have hs2 : s + 2 ≤ (s + 2) ^ (C + 2) := Nat.le_self_pow (by omega) _
  have hC : C + 2 ≤ 2 * (C + 2) * (s + 2) ^ (C + 2) := by nlinarith
  have hEM : expE C s ≤ M := by unfold expE; nlinarith
  have hPM : 2 * P ≤ M := by nlinarith
  have hs : Val w (add (lvl 2) (const 2)) [s, n, P] (s + 2) :=
    val_add (ThreeSat.val_x3 s n) (val_const 2 _)
  have hbs : Bd w M (add (lvl 2) (const 2)) [s, n, P] :=
    bd_add (bd_lvl _ _) (bd_const (by omega) _) (ThreeSat.val_x3 s n) (val_const 2 _) (by nlinarith)
  have hE : Val w (expT C (lvl 2)) [s, n, P] (expE C s) :=
    val_mul (val_const _ _) (ThreeSat.val_powC (C + 2) hs)
  have hbE : Bd w M (expT C (lvl 2)) [s, n, P] :=
    bd_mul (bd_const (by omega) _)
      (ThreeSat.bd_powC (C + 2) hs hbs (by omega) (by nlinarith) (by omega))
      (val_const _ _) (ThreeSat.val_powC (C + 2) hs) hEM
  refine bd_foldT (f := fun acc k =>
      mod (add acc (mul (call3 Q (lvl 2) (lvl 1) k) (pow2ModT k (lvl 0)))) (lvl 0))
    hE (val_const 0 _) (fun a k => (a + Q.eval w [s, n, k] * (2 ^ k % P)) % P)
    (fun pre u u' a q hu hu' => val_mod (val_add hu (val_mul
      (val_call3 hQ ((ThreeSat.val_x3 s n).ext pre) ((ThreeSat.val_y3 s n).ext pre) hu')
      (val_pow2ModT hu' ((ThreeSat.val_s3 s n).ext pre) hP))) ((ThreeSat.val_s3 s n).ext pre))
    hbE (bd_const (Nat.zero_le _) _) hEM fun pre u u' a q hq ha hu hu' hbu hbu' => ?_
  rw [foldl_residue] at ha
  have haP : a < P := ha ▸ Nat.mod_lt _ (by omega)
  have hpow : 2 ^ q % P < P := Nat.mod_lt _ (by omega)
  have hbq := hb q
  have hprod : Q.eval w [s, n, q] * (2 ^ q % P) < P := by
    calc _ ≤ 1 * (2 ^ q % P) := Nat.mul_le_mul_right _ hbq
      _ < P := by omega
  have hcall := val_call3 hQ ((ThreeSat.val_x3 s n).ext pre) ((ThreeSat.val_y3 s n).ext pre) hu'
  have hvpow := val_pow2ModT hu' ((ThreeSat.val_s3 (w := w) (s := P) s n).ext pre) hP
  refine bd_mod (bd_add hbu (bd_mul (bd_call3 hQ ((ThreeSat.val_x3 s n).ext pre)
      ((ThreeSat.val_y3 s n).ext pre) hu' (bd_lvl _ _) (bd_lvl _ _) hbu' (hQb q))
    (bd_pow2ModT hu' ((ThreeSat.val_s3 s n).ext pre) hP hbu' (bd_lvl _ _) (by omega) hPM)
    hcall hvpow (by omega)) hu (val_mul hcall hvpow) (by omega)) (bd_lvl _ _)

end Residue

/-! ### The residue form of Theorem 2.3 from the bits -/

theorem two_le_pow_sqrtLog (s : ℕ) : s + 2 ≤ 2 ^ (2 * SqrtLog s) := by
  have h1 := log2_add_one_le_sqrtLog s
  have h2 : s < 2 ^ (s.log2 + 1) := Nat.lt_log2_self
  have h3 : 2 ^ (s.log2 + 2) ≤ 2 ^ (2 * SqrtLog s) := Nat.pow_le_pow_right (by omega) (by omega)
  have h4 : 2 ^ (s.log2 + 2) = 2 * 2 ^ (s.log2 + 1) := by rw [pow_succ]; ring
  have h5 : 1 ≤ 2 ^ (s.log2 + 1) := Nat.one_le_two_pow
  omega

theorem poly_le_pow_sqrtLog (C s : ℕ) :
    2 * (C + 2) * (s + 2) ^ (C + 2) ≤ 2 ^ (4 * (C + 2) * SqrtLog s) := by
  have hsl : 1 ≤ SqrtLog s := Nat.le_add_left _ _
  have h1 : (s + 2) ^ (C + 2) ≤ 2 ^ (2 * (C + 2) * SqrtLog s) := by
    calc (s + 2) ^ (C + 2) ≤ (2 ^ (2 * SqrtLog s)) ^ (C + 2) :=
          Nat.pow_le_pow_left (two_le_pow_sqrtLog s) _
      _ = _ := by rw [← pow_mul]; ring_nf
  have h2 : 2 * (C + 2) ≤ 2 ^ (2 * (C + 2) * SqrtLog s) :=
    (Nat.lt_two_pow_self (n := 2 * (C + 2))).le.trans
      (Nat.pow_le_pow_right (by omega) (Nat.le_mul_of_pos_right _ hsl))
  calc _ ≤ 2 ^ (2 * (C + 2) * SqrtLog s) * 2 ^ (2 * (C + 2) * SqrtLog s) := Nat.mul_le_mul h2 h1
    _ = _ := by rw [← pow_add]; ring_nf

/-- **`CubeCounting` gives the residue form of Theorem 2.3** (`ThreeSat.Theorem41`), with the window
exponent `c = 0`: the residue of `Z(G)` modulo every prime `p ≤ s` is computed from its bits. -/
theorem theorem41_of_cubeCounting (h : CubeCounting) : ThreeSat.Theorem41 := fun F => by
  obtain ⟨Q, CQ, s₀, hQc, hQ⟩ := h F
  refine ⟨residueProg Q F.C, 0, CQ + 4 * (F.C + 2), s₀, closed_closeAt _ _,
    fun w s p hm hs hp _ hps => ?_⟩
  have hP : 2 ≤ p := hp.two_le
  have hsl : 1 ≤ SqrtLog s := Nat.le_add_left _ _
  have hB1 : 2 ^ (CQ * SqrtLog s) ≤ 2 ^ ((CQ + 4 * (F.C + 2)) * SqrtLog s) :=
    Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_right _ (by omega))
  have hB2 : 2 * (F.C + 2) * (s + 2) ^ (F.C + 2) ≤ 2 ^ ((CQ + 4 * (F.C + 2)) * SqrtLog s) :=
    (poly_le_pow_sqrtLog F.C s).trans
      (Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_right _ (by omega)))
  have hb : ∀ k, Q.eval w [s, w.length, k] ≤ 1 := fun k => by
    rw [(hQ w s k hm hs).1]; exact Nat.le_of_lt_succ (Nat.mod_lt _ (by omega))
  obtain ⟨hv, hbd⟩ := ThreeSat.run_closeAt (n := 3) rfl (val_residueT (w := w) hQc F.C hP)
    (bd_residueT hQc F.C hP hps hB2 hb fun k => bounded_mono hB1 _ _ (hQ w s k hm hs).2)
  refine ⟨?_, hbd⟩
  rw [residueProg, hv]
  have hsum : ∑ k ∈ range (expE F.C s), Q.eval w [s, w.length, k] * 2 ^ k =
      (F.net w s).value.toNat := by
    rw [sum_congr rfl fun k _ => by rw [(hQ w s k hm hs).1], sum_bits,
      Nat.mod_eq_of_lt (toNat_value_lt F hm)]
  rw [hsum]
  push_cast
  rw [Int.toNat_of_nonneg (value_nonneg F hm)]

end CubeCounting

open CubeCounting

/-- **Corollary 7.2 from Theorem 2.3.** One deterministic machine computes every bit of the number
of satisfying assignments of a 3-CNF formula with `m ≥ 2` clauses in which every variable occurs,
in space `O(m/√log m)` and time `2^{O(m/√log m)}`. -/
theorem cor_3sat_of_cubeCounting (h : CubeCounting) :
    ∃ C, Turing.MultiTapeTM.DecidableInTimeAndSpace ThreeSat.SmallBitLanguage ThreeSat.smallEnc
      (fun a => 2 ^ (C * SqrtLog a.1.φ.length)) (fun a => C * SqrtLog a.1.φ.length) :=
  ThreeSat.cor_9_4 (theorem41_of_cubeCounting h)

/-- **Corollary 7.2 from Theorem 2.3, every bit position.** -/
theorem cor_3sat_bits_of_cubeCounting (h : CubeCounting) :
    ∃ C, Turing.MultiTapeTM.DecidableInTimeAndSpace ThreeSat.BitLanguage ThreeSat.instEnc
      (fun a => 2 ^ (C * ThreeSat.bud a)) (fun a => C * ThreeSat.bud a) :=
  ThreeSat.cor_9_4_bits (theorem41_of_cubeCounting h)

end Cslib.Complexity.NtimeDspace.Cross
