/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Razborov.Useful
public import CslibFrontier.MachineLearning.UniformLearning.CIKK.Parameters
public import Mathlib.Data.Nat.Log

/-!
# Parameters of the CIKK learner for AC⁰[2]

Carmosino, Impagliazzo, Kabanets and Kolokolova run their learner with a natural property at an
input length `ℓ` where the property rejects every output `g_z` of the black-box generator
[Carmosino et al., Theorem 5.1, p. 10:19][CarmosinoImpagliazzoKabanetsKolokolova2016]. For AC⁰[2]
the `g_z` are the functions computed by the Nisan–Wigderson generator on the amplified target
`Amp(f) = (f^k)^GL`, and the property is the rank property, which rejects every function computed
by a circuit of depth `D` and size `S` at the input length `rankLength D x` for `S ≤ 2 ^ x`
(`Cslib.Circuits.Boolean.Razborov.notMem_rankProperty_rankLength_of_computes`). This file fixes the
three parameters of that instance in closed form, for depth `d`, size `s`, `n` input variables and
error exponent `e`:

* the size bound `S(g) = k s + 6 (k n + k)² + 3` on the circuits for `g_z`
  with `k = cikkK e g`, from a size-`s` circuit for `f`; their depth is at most `d + 7`;
* `cikkAC0Len d e n s g`: the input length `ℓ(g) = rankLength (d + 7) (⌊log₂ S(g)⌋ + 1)` at which
  the rank test rejects every function such a circuit computes
  (`notMem_rankProperty_cikkAC0Len_of_computes`);
* `cikkAC0Gap d e n s`: an advantage exponent `g`, a power of two, with `ℓ(g) + 2 ≤ g`
  (`cikkAC0Len_add_two_le_cikkAC0Gap`).

The last inequality is the fixed point of the parameters: the learner's density hypothesis needs a
property accepting a `2^{-g}` fraction of the truth tables of length `2 ^ ℓ` with `2 ^ (ℓ + 1)` to
spare, while `ℓ` grows with `g` through `k` and `S`. It replaces the source's choice of `L` with
`log L > u⁻¹(poly)` [Carmosino et al., proof of Theorem 5.1, p. 10:19]
[CarmosinoImpagliazzoKabanetsKolokolova2016]. Since `ℓ` is polylogarithmic in `S` and `k` is linear
in `g`, `g` is polylogarithmic in `n`, `s` and `2 ^ e` for fixed `d`: with `D = d + 7` and
`B = ⌊log₂ (M² (s + 6 (n + 1)² + 3))⌋ + 1`, `M = 2^{e+10} (3e + 42)`,
`g ≤ 2^{2D(5D+25)} B^{2D}` (`cikkAC0Gap_le`). That bound makes the learner's number of queries
quasi-polynomial (`CslibFrontier.MachineLearning.UniformLearning.CIKK.AC0Mod`); the source's
[Carmosino et al., Corollary 5.4, p. 10:20][CarmosinoImpagliazzoKabanetsKolokolova2016] bounds the
running time, which this library does not certify.

Labels. The rank property is this library's variant (one square matrix, threshold `C(n, a) / 2`,
level `sliceLevel`; see `Cslib.Circuits.Boolean.Razborov.RankProperty`), and only `p = 2` is
covered, where Corollary 5.4 states every prime. The depth overhead `7` is that of the library's
generator circuits (`Cslib.Crypto.PRG.NisanWigderson.exists_circuit_generator_glAmp`). `g` and `k`
are powers of two, and all constants are this library's, far from optimal. The learner and its
correctness for depth-`d`, size-`s` AC⁰[2] targets are in
`CslibFrontier.MachineLearning.UniformLearning.CIKK.AC0Mod`; this file proves only the parameter
inequalities.

## Main definitions

* `Cslib.Circuits.Boolean.Razborov.cikkAC0Len`: the input length `ℓ(g)`.
* `Cslib.Circuits.Boolean.Razborov.cikkAC0Gap`: the advantage exponent `g`.

## Main results

* `Cslib.Circuits.Boolean.Razborov.notMem_rankProperty_cikkAC0Len_of_computes`: at the length
  `ℓ(g)`, no circuit with `MOD_2` gates of depth at most `d + 7` and size at most `S(g)` computes a
  member of the rank property.
* `Cslib.Circuits.Boolean.Razborov.cikkAC0Len_add_two_le_cikkAC0Gap`: the fixed point
  `ℓ(g) + 2 ≤ g`.
* `Cslib.Circuits.Boolean.Razborov.cikkAC0Gap_le`: `g ≤ 2^{2D(5D+25)} B^{2D}`.

## References

* [M. L. Carmosino, R. Impagliazzo, V. Kabanets, A. Kolokolova, *Learning algorithms from natural
  proofs*, Theorem 5.1 (p. 10:19) and Corollary 5.4 (p. 10:20)]
  [CarmosinoImpagliazzoKabanetsKolokolova2016]
-/

public section

namespace Cslib.Circuits.Boolean.Razborov

open Cslib.MachineLearning.UniformLearning

/-- The size bound `S(g) = k s + 6 (k n + k)² + 3`, with `k = cikkK e g`, on the circuits for the
generator outputs `g_z` built from a circuit of size `s` on `n` inputs. -/
private def cikkAC0Size (e n s g : ℕ) : ℕ := cikkK e g * s + 6 * (cikkK e g * n + cikkK e g) ^ 2 + 3

/-- The input length `ℓ(g) = rankLength (d + 7) (⌊log₂ S(g)⌋ + 1)` at which the rank test rejects
every function computed by a circuit with `MOD_2` gates of depth at most `d + 7` and size at most
`S(g)`. -/
def cikkAC0Len (d e n s g : ℕ) : ℕ := rankLength (d + 7) (Nat.log 2 (cikkAC0Size e n s g) + 1)

/-- `B = ⌊log₂ (M² (s + 6 (n + 1)² + 3))⌋ + 1` with `M = 2^{e+10} (3e + 42)`, the number of bits
of the part of `S(g)` that does not depend on `g`. -/
private def cikkAC0Bits (e n s : ℕ) : ℕ :=
  Nat.log 2 ((2 ^ (e + 10) * (3 * e + 42)) ^ 2 * (s + 6 * (n + 1) ^ 2 + 3)) + 1

/-- The exponent `2D (⌊log₂ B⌋ + 5D + 25)` of `cikkAC0Gap`, with `D = d + 7`. -/
private def cikkAC0Exp (d e n s : ℕ) : ℕ :=
  2 * (d + 7) * (Nat.log 2 (cikkAC0Bits e n s) + 5 * (d + 7) + 25)

/-- The advantage exponent `g = 2^{2D (⌊log₂ B⌋ + 5D + 25)}`, with `D = d + 7` and `B` the number of
bits of `M² (s + 6 (n + 1)² + 3)`, `M = 2^{e+10} (3e + 42)`. It satisfies `ℓ(g) + 2 ≤ g`
(`cikkAC0Len_add_two_le_cikkAC0Gap`). -/
def cikkAC0Gap (d e n s : ℕ) : ℕ := 2 ^ cikkAC0Exp d e n s

/-! ### The rank test rejects the generator circuits -/

/-- **The rank test rejects the generator circuits**: at the length `cikkAC0Len d e n s g`, no
circuit with `MOD_2` gates of depth at most `d + 7` and size at most `S(g)` computes a function of
the rank property. -/
theorem notMem_rankProperty_cikkAC0Len_of_computes {d e n s g : ℕ}
    {G : Circuit Unbounded.extSignature (cikkAC0Len d e n s g) 1} (hGd : G.depth ≤ d + 7)
    (hGs : G.size ≤ cikkK e g * s + 6 * (cikkK e g * n + cikkK e g) ^ 2 + 3)
    {f : BooleanFunction (cikkAC0Len d e n s g)}
    (hG : G.Computes (Unbounded.extInterpretation (modGate 2)) (single f)) :
    f ∉ rankProperty sliceLevel (cikkAC0Len d e n s g) :=
  notMem_rankProperty_rankLength_of_computes (x := Nat.log 2 (cikkAC0Size e n s g) + 1) hGd
    (hGs.trans (Nat.lt_pow_succ_log_self (by norm_num) (cikkAC0Size e n s g)).le) hG

/-! ### The fixed point -/

/-- `S(2 ^ r) < 2 ^ (2 r + B)`. -/
private theorem cikkAC0Size_lt (e n s r : ℕ) :
    cikkAC0Size e n s (2 ^ r) < 2 ^ (2 * r + cikkAC0Bits e n s) := by
  set g := 2 ^ r
  have hg : 1 ≤ g := Nat.one_le_two_pow
  set M := 2 ^ (e + 10) * (3 * e + 42)
  have hk : cikkK e g ≤ M * g := (cikkK_le e g).trans <| by
    rw [mul_assoc]
    exact Nat.mul_le_mul_left _ (by nlinarith)
  have hM : 1 ≤ (M * g) ^ 2 := Nat.one_le_pow _ _ (Nat.mul_pos (by positivity) hg)
  have hMg : cikkK e g ≤ (M * g) ^ 2 := hk.trans (Nat.le_self_pow two_ne_zero _)
  have h2 : (cikkK e g * n + cikkK e g) ^ 2 ≤ (M * g * (n + 1)) ^ 2 :=
    Nat.pow_le_pow_left (by simpa [Nat.mul_succ] using Nat.mul_le_mul_right (n + 1) hk) 2
  have hle : cikkAC0Size e n s g ≤ g ^ 2 * (M ^ 2 * (s + 6 * (n + 1) ^ 2 + 3)) := by
    unfold cikkAC0Size
    calc cikkK e g * s + 6 * (cikkK e g * n + cikkK e g) ^ 2 + 3
        ≤ (M * g) ^ 2 * s + 6 * (M * g * (n + 1)) ^ 2 + 3 * (M * g) ^ 2 :=
          Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_right _ hMg) (Nat.mul_le_mul_left 6 h2))
            ((Nat.mul_one 3).symm.le.trans (Nat.mul_le_mul_left 3 hM))
      _ = g ^ 2 * (M ^ 2 * (s + 6 * (n + 1) ^ 2 + 3)) := by ring
  have hW : M ^ 2 * (s + 6 * (n + 1) ^ 2 + 3) < 2 ^ cikkAC0Bits e n s :=
    Nat.lt_pow_succ_log_self (by norm_num) _
  exact (hle.trans_lt (Nat.mul_lt_mul_of_pos_left hW (by positivity))).trans_eq
    (by rw [← pow_mul, ← pow_add, mul_comm r 2])

/-- With `q = ⌊log₂ B⌋ + 5D + 25`: `2 · 2^{2D+7} (4 D q + B) ≤ 2 ^ q`. -/
private theorem two_mul_le_two_pow (D B : ℕ) :
    2 * (2 ^ (2 * D + 7) * (2 * (2 * D * (Nat.log 2 B + 5 * D + 25)) + B)) ≤
      2 ^ (Nat.log 2 B + 5 * D + 25) := by
  have hb : Nat.log 2 B < 2 ^ Nat.log 2 B := Nat.lt_two_pow_self
  have hB : B < 2 * 2 ^ Nat.log 2 B := by
    simpa [pow_succ, mul_comm] using Nat.lt_pow_succ_log_self (by norm_num) B
  have hD : D < 2 ^ D := Nat.lt_two_pow_self
  have e1 : 2 ^ (2 * D + 7) = 2 ^ D * 2 ^ D * 128 := by
    rw [show 2 * D + 7 = D + D + 7 by ring, pow_add, pow_add]
    norm_num
  rw [e1, pow_add, pow_add, pow_mul']
  generalize Nat.log 2 B = b at hb hB ⊢
  generalize 2 ^ b = t at hb hB ⊢
  generalize 2 ^ D = u at hD ⊢
  have ht : 0 < t := by omega
  have hu : 0 < u := by omega
  have hDb : D * b ≤ t * u ^ 3 := (Nat.mul_le_mul hD.le hb.le).trans <| by
    rw [show t * u ^ 3 = (u * t) * (u * u) by ring]
    exact Nat.le_mul_of_pos_right _ (by positivity)
  have hDD : D * D ≤ t * u ^ 3 := (Nat.mul_le_mul hD.le hD.le).trans <| by
    rw [show t * u ^ 3 = (u * u) * (t * u) by ring]
    exact Nat.le_mul_of_pos_right _ (by positivity)
  have hDu : D ≤ t * u ^ 3 := hD.le.trans <| by
    rw [show t * u ^ 3 = u * (t * u ^ 2) by ring]
    exact Nat.le_mul_of_pos_right _ (by positivity)
  have htu : t ≤ t * u ^ 3 := Nat.le_mul_of_pos_right _ (by positivity)
  have hin : 2 * (2 * D * (b + 5 * D + 25)) + B ≤ 131072 * (t * u ^ 3) := by linarith
  calc 2 * (u * u * 128 * (2 * (2 * D * (b + 5 * D + 25)) + B))
      = 256 * (u * u) * (2 * (2 * D * (b + 5 * D + 25)) + B) := by ring
    _ ≤ 256 * (u * u) * (131072 * (t * u ^ 3)) := Nat.mul_le_mul_left _ hin
    _ = t * u ^ 5 * 2 ^ 25 := by ring

/-- **The fixed point, abstractly**: for `D ≥ 7` and `0 < S < 2 ^ (2 r + B)` with
`r = 2D (⌊log₂ B⌋ + 5D + 25)`, `rankLength D (⌊log₂ S⌋ + 1) + 2 ≤ 2 ^ r`. -/
private theorem rankLength_log_add_two_le {D B S : ℕ} (hD : 7 ≤ D) (hS0 : S ≠ 0)
    (hS : S < 2 ^ (2 * (2 * D * (Nat.log 2 B + 5 * D + 25)) + B)) :
    rankLength D (Nat.log 2 S + 1) + 2 ≤ 2 ^ (2 * D * (Nat.log 2 B + 5 * D + 25)) := by
  have hx : Nat.log 2 S + 1 ≤ 2 * (2 * D * (Nat.log 2 B + 5 * D + 25)) + B :=
    Nat.log_lt_of_lt_pow hS0 hS
  have hx1 : 1 ≤ Nat.log 2 S + 1 := Nat.le_add_left 1 _
  have hlen := rankLength_add_one_le (d := D) hx1
  have hkey := two_mul_le_two_pow D B
  generalize Nat.log 2 B + 5 * D + 25 = q at hx hkey ⊢
  generalize Nat.log 2 S + 1 = x at hx hx1 hlen ⊢
  have hZ : 1 ≤ 2 * (2 * D * q) + B := by omega
  generalize 2 * (2 * D * q) + B = Z at hx hkey hZ
  have e : (2 ^ (2 * D + 7) * Z) ^ (2 * D) = 2 ^ (2 * D * (2 * D + 7)) * Z ^ (2 * D) := by
    rw [mul_pow, ← pow_mul, mul_comm (2 * D + 7)]
  have h1 : rankLength D x + 1 ≤ 401 * (2 ^ (2 * D + 7) * Z) ^ (2 * D) := by
    calc rankLength D x + 1 ≤ 401 * 2 ^ (2 * D * (2 * D + 7)) * x ^ (2 * D) := hlen
      _ ≤ 401 * 2 ^ (2 * D * (2 * D + 7)) * Z ^ (2 * D) := by gcongr
      _ = 401 * (2 ^ (2 * D + 7) * Z) ^ (2 * D) := by rw [e, mul_assoc 401]
  have hY : 0 < 2 ^ (2 * D + 7) * Z := Nat.mul_pos (by positivity) hZ
  generalize 2 ^ (2 * D + 7) * Z = Y at h1 hkey hY
  have hYp : 1 ≤ Y ^ (2 * D) := Nat.one_le_pow _ _ hY
  have h2 : 402 * Y ^ (2 * D) ≤ (2 * Y) ^ (2 * D) := by
    rw [mul_pow]
    exact Nat.mul_le_mul_right _
      (le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega : 14 ≤ 2 * D)))
  have h3 : (2 * Y) ^ (2 * D) ≤ 2 ^ (2 * D * q) := by
    rw [mul_comm (2 * D) q, pow_mul 2 q (2 * D)]
    exact Nat.pow_le_pow_left hkey _
  omega

/-- **The fixed point of the parameters**: `ℓ(g) + 2 ≤ g` for `g = cikkAC0Gap d e n s` and
`ℓ(g) = cikkAC0Len d e n s g`. This is the condition under which the rank test's density
`1 / 2` covers the learner's density hypothesis `2^{2^ℓ} 2^{ℓ+1} ≤ 2^g · #{accepted}`. -/
theorem cikkAC0Len_add_two_le_cikkAC0Gap (d e n s : ℕ) :
    cikkAC0Len d e n s (cikkAC0Gap d e n s) + 2 ≤ cikkAC0Gap d e n s := by
  unfold cikkAC0Len cikkAC0Gap cikkAC0Exp
  refine rankLength_log_add_two_le (by omega) ?_ (cikkAC0Size_lt e n s _)
  unfold cikkAC0Size
  omega

/-- **`g` is polylogarithmic**: with `D = d + 7`, `M = 2^{e+10} (3e + 42)` and
`B = ⌊log₂ (M² (s + 6 (n + 1)² + 3))⌋ + 1`, `cikkAC0Gap d e n s ≤ 2^{2D(5D+25)} B^{2D}`. For fixed
`d`, `g` is polylogarithmic in `n`, `s` and `2 ^ e`. -/
theorem cikkAC0Gap_le (d e n s : ℕ) :
    cikkAC0Gap d e n s ≤ 2 ^ (2 * (d + 7) * (5 * (d + 7) + 25)) *
      (Nat.log 2 ((2 ^ (e + 10) * (3 * e + 42)) ^ 2 * (s + 6 * (n + 1) ^ 2 + 3)) + 1) ^
        (2 * (d + 7)) := by
  unfold cikkAC0Gap cikkAC0Exp cikkAC0Bits
  have hB1 : 1 ≤ Nat.log 2 ((2 ^ (e + 10) * (3 * e + 42)) ^ 2 * (s + 6 * (n + 1) ^ 2 + 3)) + 1 :=
    Nat.le_add_left 1 _
  generalize Nat.log 2 ((2 ^ (e + 10) * (3 * e + 42)) ^ 2 * (s + 6 * (n + 1) ^ 2 + 3)) + 1 = B
    at hB1 ⊢
  have hB : 2 ^ Nat.log 2 B ≤ B := Nat.pow_log_le_self 2 (by omega)
  generalize d + 7 = D
  calc 2 ^ (2 * D * (Nat.log 2 B + 5 * D + 25))
      = 2 ^ (2 * D * (5 * D + 25)) * (2 ^ Nat.log 2 B) ^ (2 * D) := by ring
    _ ≤ 2 ^ (2 * D * (5 * D + 25)) * B ^ (2 * D) := by gcongr

end Cslib.Circuits.Boolean.Razborov
