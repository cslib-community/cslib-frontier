/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.CountingScale
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.ScaleInterface
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.ThreeSatFinal
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Algebra.Order.Star.Real

/-!
# Counting 3-SAT from Theorem 2.3 at a general space bound

The first paragraph of the paper's §8 (`sec:discussion`): *a procedure that computes the value of
every network with logspace access in space `D(s)` also counts the satisfying assignments of a
3-CNF formula with `m` clauses in time `2^{O(D(O(m)))}`, by the reduction of Corollary 7.2.
Proving `NTIME[t] ⊆ SPACE[t/log t]` that way would therefore count them in time `2^{O(m/log m)}`
[…]. Space `t^{1−ε}` would count them in time `2^{O(m^{1−ε})}`.*

The procedure is `CubeCountingAt D` (Theorem 2.3 in bit form with `D s` for `SqrtLog s`,
`CountingScale.lean`). The reduction is that of Corollary 7.2 (`ThreeSatFinal.lean`), here taken
directly in bits, with no residues: on the encoding of a formula `φ` with `m` clauses and a bit
position `j ≤ 3m` (all bits of the count, which is at most `2^{3m}`), the decider reads `m` and `j`
and runs the program of `CubeCountingAt D` for `threeSatFamily` at size `s = 8m + K` on `j`; the
network of `φ` at that size has value `#SAT(φ)` (`threeSatFamily_value`). Compiling the program
(`ProgLang.decidable_of_prog_len`) gives a multitape machine.

The only hypothesis on `D` for the general statement is an eventual logarithmic lower bound
`log₂ n + 1 ≤ D n` for `n ≥ N`. It pays for reading the input: the input has length polynomial in
`m`, and a machine of space `C · D(s)` must hold a position in it. It is only needed eventually
because `K` can be taken at least `N`.

## Main results

* `smallBits_at`: `CubeCountingAt D` gives a decider of `SmallBitLanguage` (bit `j ≤ 3m` of
  `#SAT(φ)`) in time `2^(C · D(8m + K))` and space `C · D(8m + K)`: the paper's
  `2^{O(D(O(m)))}`.
* `smallBits_at_mono`: for monotone `D`, time `2^(C · D(C · m))` and space `C · D(C · m)`.
* `smallBits_of_linear`, `smallBits_of_scale`: when `D(8m + K) = O(D m)` for every `K` (for
  instance under `Scale D`), time `2^(C · D m)` and space `C · D m`. With `cubeCountingAt_sqrtLog`
  and `scale_sqrtLog` this recovers the shape of `cor_9_4`.
* `smallBits_nlog`: at `D n = n / (log₂ n + 1) + 1` (space `t / log t`), time
  `2^(C · (m / (log₂ m + 1) + 1))`, i.e. `2^{O(m/log m)}`.
* `smallBits_rpow`: at `D n = ⌊n^(1-ε)⌋ + 1` for real `0 ≤ ε < 1` (space `t^{1-ε}`), time
  `2^(C · (⌊m^(1-ε)⌋ + 1))`, i.e. `2^{O(m^{1-ε})}`.

Every bound has the same constant `C` in time and space, and the machine is fixed before the
instance. The results are conditional on `CubeCountingAt D`, as in the paper.

## References

* The paper (`separating-ntime-from-space.tex`), §7, Corollary 7.2 (`cor:3sat`); §8
(`sec:discussion`), first
  paragraph.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Cross.ThreeSat

open NtimeDspace.ProgLang NtimeDspace.ProgTerm Term NtimeDspace.Cross.Exact Finset
  _root_.Turing.MultiTapeTM NtimeDspace.SumProduct Filter

/-! ### Sizes -/

/-- For a bit position `j ≤ 3m` the input fits the 3-SAT family at size `8m + K`. -/
theorem len_le_bnd_of_small (a : Instance) (hj : a.j ≤ 3 * a.φ.length) (K : ℕ) :
    (instEnc a).length ≤ bnd (8 * a.φ.length + K) := by
  have hsz : (encNat a.j).length ≤ Nat.log 2 (3 * a.φ.length + 1) + 1 := by
    rw [encNat_apply, Nat.size_eq_bits_len, Nat.size_le]
    exact (show a.j < 3 * a.φ.length + 1 by omega).trans (Nat.lt_pow_succ_log_self (by norm_num) _)
  exact (len_small hsz).trans (aux_sq _ K (by have := a.two_le; omega))

/-- A length within `bnd s` is below `2^(4d)` when `log₂ s + 1 ≤ d`. -/
theorem lt_two_pow_of_le_bnd {n s d : ℕ} (hn : n ≤ bnd s) (hd : s.log2 + 1 ≤ d) :
    n < 2 ^ (4 * d) := by
  have hsd : s < 2 ^ d := Nat.lt_log2_self.trans_le (Nat.pow_le_pow_right (by norm_num) hd)
  have h2 : 2 ≤ 2 ^ d := by
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show 1 ≤ d by omega); simpa using this
  have h1 : s + 2 < 2 ^ (d + 1) := by rw [pow_succ]; omega
  calc n ≤ (s + 2) ^ 2 := hn
    _ < (2 ^ (d + 1)) ^ 2 := Nat.pow_lt_pow_left h1 (by norm_num)
    _ = 2 ^ (2 * d + 2) := by rw [← pow_mul]; ring_nf
    _ ≤ 2 ^ (4 * d) := Nat.pow_le_pow_right (by norm_num) (by omega)

/-! ### The decider -/

/-- **The decider on small instances**, on `[|w|]`: bit `j` of the count, by the bit program `Q`
at size `s = 8m + K'`. -/
def smallDeciderT (Q : Prog) (K' : ℕ) : Term := call3 Q (szT K') (lvl 0) jT

/-- The decider as a program closed in `[|w|]`. -/
def smallDecider (Q : Prog) (K' : ℕ) : Prog := closeAt 1 (smallDeciderT Q K' 1)

/-- The decider on an instance with `j ≤ 3m`, from a bit program `Q` for the 3-SAT family with
values below `2^(C · D s)`: it decides `BitLanguage`, with values below `2^((C + 26) · D s)` at
`s = 8m + K'`. -/
theorem smallDecider_spec {D : ℕ → ℕ} {Q : Prog} {C s₀ K' : ℕ} (hQc : Prog'.closed 3 Q = true)
    (hQ : ∀ (w : List Bool) (s j : ℕ), threeSatFamily.Mem w s → s₀ ≤ s →
      Q.eval w [s, w.length, j] = (threeSatFamily.net w s).value.toNat / 2 ^ j % 2 ∧
        Q.Bounded w (2 ^ (C * D s)) [s, w.length, j])
    (hK : s₀ ≤ K') (a : Instance) (hj : a.j ≤ 3 * a.φ.length)
    (hlog : (8 * a.φ.length + K').log2 + 1 ≤ D (8 * a.φ.length + K')) :
    (smallDecider Q K').Bounded (instEnc a) (2 ^ ((C + 26) * D (8 * a.φ.length + K')))
        [(instEnc a).length] ∧
      (1 ≤ (smallDecider Q K').eval (instEnc a) [(instEnc a).length] ↔ a ∈ BitLanguage) := by
  have hlen0 := len_le_bnd_of_small a hj K'
  -- notation and sizes
  obtain ⟨w, hw⟩ : ∃ w, w = instEnc a := ⟨_, rfl⟩
  obtain ⟨n, hn⟩ : ∃ n, n = w.length := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m, m = a.φ.length := ⟨_, rfl⟩
  obtain ⟨lj, hlj⟩ : ∃ lj, lj = (encNat a.j).length := ⟨_, rfl⟩
  obtain ⟨Lb, hLb⟩ : ∃ Lb, Lb = Nat.log 2 (3 * m + 1) + 1 := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s, s = 8 * m + K' := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d, d = D s := ⟨_, rfl⟩
  obtain ⟨Mf, hMf⟩ : ∃ Mf, Mf = 2 ^ ((C + 26) * d) := ⟨_, rfl⟩
  rw [← hm, ← hs, ← hd] at hlog
  rw [← hw, ← hm, ← hs] at hlen0
  rw [← hn] at hlen0
  rw [← hw, ← hn, ← hm, ← hs, ← hd, ← hMf]
  have hm2 : 2 ≤ m := hm ▸ a.two_le
  have hj' : a.j ≤ 3 * m := hm ▸ hj
  have hmn : m ≤ n := by rw [hm, hn, hw]; exact m_le_len a
  have hd1 : 1 ≤ d := by omega
  have hsd : s < 2 ^ d := Nat.lt_log2_self.trans_le (Nat.pow_le_pow_right (by norm_num) hlog)
  have hdM : 2 ^ d ≤ Mf := by
    rw [hMf]; exact Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_of_pos_left _ (by omega))
  have hnd : n < 2 ^ (4 * d) := lt_two_pow_of_le_bnd hlen0 hlog
  have hN1 : 64 * (n + 2) ^ 4 ≤ Mf := (pow_four_le hnd).trans (by
    rw [hMf]; refine Nat.pow_le_pow_right (by norm_num) ?_
    have : 26 * d ≤ (C + 26) * d := Nat.mul_le_mul_right _ (by omega)
    omega)
  have hSz : Sz n Mf := ⟨hN1⟩
  have hnM : 64 * (n + 2) ≤ Mf := by
    have : (n + 2) ≤ (n + 2) ^ 4 := Nat.le_self_pow (by norm_num) _
    omega
  -- the bit position has few digits
  have hsmall : lj ≤ Lb := by
    rw [hlj, hLb, encNat_apply, Nat.size_eq_bits_len, Nat.size_le]
    exact (show a.j < 3 * m + 1 by omega).trans (Nat.lt_pow_succ_log_self (by norm_num) _)
  -- values
  have hvs : Val w (lvl 0) [n] n := val_s1
  have hraw : (rawW w n).m = m := by rw [hm, hn, hw]; exact mW_inst a
  have hvm : Val w mmT [n] m := by have := val_mT (sT := lvl 0) (s := n) hvs; rwa [hraw] at this
  have hoff : offW w n = 2 * lj + 1 := by rw [hlj, hn, hw]; exact offW_inst a
  have hvlj : Val w ljT [n] lj := by
    have := val_div (val_sub (val_offT (sT := lvl 0) hvs) (val_const 1 [n])) (val_const 2 [n])
    rw [hoff] at this
    refine fun extra => (this extra).trans ?_
    omega
  have hbm : Bd w Mf mmT [n] := bd_mT hvs (bd_lvl _ _) hSz
  have hboff : Bd w Mf (offT (lvl 0)) [n] := bd_offT hvs (bd_lvl _ _) hSz
  have hblj : Bd w Mf ljT [n] :=
    bd_div (bd_sub hboff (bd_const (by omega) _)) (bd_const (by omega) _)
  -- the bit position
  have hfv : FVal w (fun k => input (add (mul (const 2) k) (const 1))) [n]
      (fun k => ib w (2 * k + 1)) := fun pre u q hu =>
    val_input (val_add (val_mul (val_const 2 _) hu) (val_const 1 _))
  have hvj : Val w jT [n] a.j := by
    have := val_ofBitsT hvlj hfv
    have e : TermBlocks.bitsNum lj (fun k => ib w (2 * k + 1)) = a.j := by
      rw [hlj, hw, instEnc_apply, bitsNum_frame_encNat]
    rw [e] at this; exact this
  have h2lj : 2 ^ lj ≤ 6 * m + 2 := by
    calc 2 ^ lj ≤ 2 ^ Lb := Nat.pow_le_pow_right (by norm_num) hsmall
      _ ≤ 2 * (3 * m + 1) := by
        rw [hLb, pow_succ, mul_comm]
        exact Nat.mul_le_mul_left _ (Nat.pow_log_le_self 2 (by omega))
      _ = 6 * m + 2 := by ring
  have hljle : lj ≤ 2 ^ lj := Nat.lt_two_pow_self.le
  have hbj : Bd w Mf jT [n] := bd_ofBitsT hvlj hblj hfv (fun pre u q hq hu hbu =>
    bd_input (bd_add (bd_mul (bd_const (by omega) _) hbu (val_const 2 _) hu (by omega))
      (bd_const (by omega) _) (val_mul (val_const 2 _) hu) (val_const 1 _) (by omega)))
    (by omega) (by omega)
  -- the size
  have hvsz : Val w (szT K') [n] s := by
    rw [hs]; exact val_add (val_mul (val_const 8 _) hvm) (val_const K' _)
  have hbsz : Bd w Mf (szT K') [n] :=
    bd_add (bd_mul (bd_const (by omega) _) hbm (val_const 8 _) hvm (by omega))
      (bd_const (by omega) _) (val_mul (val_const 8 _) hvm) (val_const K' _) (by omega)
  -- the bit, by the bit program for the 3-SAT family at size `s`
  have hmem : threeSatFamily.Mem w s := by show w.length ≤ bnd s; rw [← hn]; exact hlen0
  obtain ⟨hQe, hQb⟩ := hQ w s a.j hmem (by omega)
  have hlen' : (Turing.MultiTapeTM.frame (encNat a.j) ++ encSlots a.φ).length ≤ bnd s := by
    rw [← instEnc_apply, ← hw, ← hn]; exact hlen0
  have hval := threeSatFamily_value (encNat a.j) a.φ s a.three a.occurs hlen' (by omega)
  rw [← instEnc_apply, ← hw] at hval
  rw [hval, ← hn, Int.toNat_natCast] at hQe
  rw [← hn, ← hd] at hQb
  have hQM : 2 ^ (C * d) ≤ Mf := by
    rw [hMf]; exact Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ (by omega))
  have hv1 : Val w (smallDeciderT Q K') [n] (numModels a.φ / 2 ^ a.j % 2) := by
    rw [← hQe]; exact val_call3 hQc hvsz hvs hvj
  have hb1 : Bd w Mf (smallDeciderT Q K') [n] :=
    bd_call3 hQc hvsz hvs hvj hbsz (bd_lvl _ _) hbj (bounded_mono hQM _ _ hQb)
  obtain ⟨he, hb⟩ := run_closeAt rfl hv1 hb1
  have he' : (smallDecider Q K').eval w [n] = numModels a.φ / 2 ^ a.j % 2 := he
  have hb' : (smallDecider Q K').Bounded w Mf [n] := hb
  refine ⟨hb', ?_⟩
  rw [he', ← Nat.toNat_testBit]
  simp only [BitLanguage, Set.mem_ofPred_eq]
  cases (numModels a.φ).testBit a.j <;> simp

/-! ### Counting 3-SAT at the space bound `D` -/

/-- **Counting 3-SAT from Theorem 2.3 at the space bound `D`** (paper §8): if Theorem 2.3 holds in
bit form at the space bound `D` (`CubeCountingAt D`), and `log₂ n + 1 ≤ D n` for large `n`, then
one machine, fixed before the instance, decides from the encoding of a 3-CNF formula `φ` with
`m ≥ 2` clauses in which every variable occurs and of a bit position `j ≤ 3m` whether bit `j` of
the number of satisfying assignments of `φ` is `1`, in time `2^(C · D(8m + K))` and space
`C · D(8m + K)`. -/
theorem smallBits_at {D : ℕ → ℕ} (hQ : CubeCountingAt D)
    (hD : ∃ N, ∀ n, N ≤ n → n.log2 + 1 ≤ D n) :
    ∃ C K, DecidableInTimeAndSpace SmallBitLanguage smallEnc
      (fun a => 2 ^ (C * D (8 * a.1.φ.length + K))) (fun a => C * D (8 * a.1.φ.length + K)) := by
  obtain ⟨Q, C, s₀, hQc, hQ⟩ := hQ threeSatFamily
  obtain ⟨N, hN⟩ := hD
  have hlog : ∀ a : SmallInstance, (8 * a.1.φ.length + (s₀ + N)).log2 + 1 ≤
      D (8 * a.1.φ.length + (s₀ + N)) := fun a => hN _ (by omega)
  have key (a : SmallInstance) := smallDecider_spec hQc hQ (K' := s₀ + N) (by omega) a.1 a.2
      (hlog a)
  have hlt (a : SmallInstance) : (smallEnc a).length < 2 ^ (4 * D (8 * a.1.φ.length + (s₀ + N))) :=
    lt_two_pow_of_le_bnd (len_le_bnd_of_small a.1 a.2 _) (hlog a)
  have hd1 (a : SmallInstance) : 1 ≤ D (8 * a.1.φ.length + (s₀ + N)) := by
    have := hlog a; omega
  obtain ⟨C', hC'⟩ := decidable_of_prog_len SmallBitLanguage (smallDecider Q (s₀ + N))
    (fun a => 4 * D (8 * a.1.φ.length + (s₀ + N)))
    (fun a => (C + 26) * D (8 * a.1.φ.length + (s₀ + N))) (C + 26)
    (fun a => by
      have h := hlt a
      have hne : (smallEnc a).length ≠ 0 := by
        have := m_le_len a.1; have := a.1.two_le
        show (instEnc a.1).length ≠ 0; omega
      have := (Nat.log2_lt hne).mpr h
      omega)
    (fun a => Nat.mul_pos (by omega) (hd1 a))
    (fun a => Nat.mul_le_mul_left _ (by omega))
    (fun a => (hlt a).le.trans (Nat.pow_le_pow_right (by norm_num)
      (Nat.mul_le_mul_right _ (by omega))))
    (fun a => (key a).1) (fun a => (key a).2)
  refine ⟨C' * 4, s₀ + N, ?_⟩
  simpa only [mul_assoc] using hC'

/-- **Counting 3-SAT at a monotone space bound `D`**: time `2^(C · D(C · m))` and space
`C · D(C · m)`, the paper's `2^{O(D(O(m)))}`. -/
theorem smallBits_at_mono {D : ℕ → ℕ} (hQ : CubeCountingAt D) (hmono : Monotone D)
    (hD : ∃ N, ∀ n, N ≤ n → n.log2 + 1 ≤ D n) :
    ∃ C, DecidableInTimeAndSpace SmallBitLanguage smallEnc
      (fun a => 2 ^ (C * D (C * a.1.φ.length))) (fun a => C * D (C * a.1.φ.length)) := by
  obtain ⟨C, K, h⟩ := smallBits_at hQ hD
  have hle (a : SmallInstance) : C * D (8 * a.1.φ.length + K) ≤
      (C + K + 8) * D ((C + K + 8) * a.1.φ.length) := by
    have hm := a.1.two_le
    have h1 : 8 * a.1.φ.length + K ≤ (C + K + 8) * a.1.φ.length := by nlinarith
    exact Nat.mul_le_mul (by omega) (hmono h1)
  exact ⟨C + K + 8, ComputableInTimeAndSpace.mono h
    (fun a => Nat.pow_le_pow_right (by norm_num) (hle a)) hle⟩

/-- **Counting 3-SAT at a space bound with linear changes of argument**: if `D(8m + K) = O(D m)`
for every `K` and `log₂ n + 1 ≤ D n` for large `n`, time `2^(C · D m)` and space `C · D m`. -/
theorem smallBits_of_linear {D : ℕ → ℕ} (hQ : CubeCountingAt D)
    (hD : ∃ N, ∀ n, N ≤ n → n.log2 + 1 ≤ D n)
    (hlin : ∀ K, ∃ c, ∀ m, 1 ≤ m → D (8 * m + K) ≤ c * D m) :
    ∃ C, DecidableInTimeAndSpace SmallBitLanguage smallEnc
      (fun a => 2 ^ (C * D a.1.φ.length)) (fun a => C * D a.1.φ.length) := by
  obtain ⟨C, K, h⟩ := smallBits_at hQ hD
  obtain ⟨c, hc⟩ := hlin K
  have hle (a : SmallInstance) : C * D (8 * a.1.φ.length + K) ≤ C * c * D a.1.φ.length := by
    rw [mul_assoc]; exact Nat.mul_le_mul_left _ (hc _ (by have := a.1.two_le; omega))
  exact ⟨C * c, ComputableInTimeAndSpace.mono h
    (fun a => Nat.pow_le_pow_right (by norm_num) (hle a)) hle⟩

/-- **Counting 3-SAT at a regular space bound** (`Scale D`, the regularity used for Theorem 2.4):
time `2^(C · D m)` and space `C · D m`. -/
theorem smallBits_of_scale {D : ℕ → ℕ} (hQ : CubeCountingAt D) (hD : Scale D) :
    ∃ C, DecidableInTimeAndSpace SmallBitLanguage smallEnc
      (fun a => 2 ^ (C * D a.1.φ.length)) (fun a => C * D a.1.φ.length) :=
  smallBits_of_linear hQ ⟨0, fun n _ => hD.log_le n⟩
    fun K => ⟨2 * (8 + K + 1), fun _ _ => hD.linear 8 K (by norm_num) le_rfl⟩

/-! ### Space `t / log t` -/

theorem mul_succ_le_two_pow {L : ℕ} (h : 5 ≤ L) : L * (L + 1) ≤ 2 ^ L := by
  induction L, h using Nat.le_induction with
  | base => norm_num
  | succ L hL ih =>
    rw [pow_succ]
    have : 2 * (L + 1) ≤ L * (L + 1) := Nat.mul_le_mul_right _ (by omega)
    nlinarith

/-- `log₂ n + 1 ≤ n / (log₂ n + 1) + 1` for `n ≥ 32`. -/
theorem log_le_div_log {n : ℕ} (hn : 32 ≤ n) : Nat.log 2 n ≤ n / (Nat.log 2 n + 1) := by
  have hL : 5 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) (by norm_num; omega)
  rw [Nat.le_div_iff_mul_le (by omega)]
  exact (mul_succ_le_two_pow hL).trans (Nat.pow_log_le_self 2 (by omega))

/-- `D(8m + K) ≤ (K + 9) D(m)` for `D n = n / (log₂ n + 1) + 1`. -/
theorem div_log_linear (m K : ℕ) :
    (8 * m + K) / (Nat.log 2 (8 * m + K) + 1) + 1 ≤ (K + 9) * (m / (Nat.log 2 m + 1) + 1) := by
  obtain ⟨L, hL⟩ : ∃ L, L = Nat.log 2 m := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, q = m / (L + 1) := ⟨_, rfl⟩
  rw [← hL, ← hq]
  have h1 : (8 * m + K) / (Nat.log 2 (8 * m + K) + 1) ≤ (8 * m + K) / (L + 1) :=
    Nat.div_le_div_left (by rw [hL]; exact Nat.add_le_add_right (Nat.log_mono_right (by omega)) _)
      (by omega)
  have hmq : m < (L + 1) * (q + 1) := by rw [hq]; exact Nat.lt_mul_div_succ m (by omega)
  have h2 : (8 * m + K) / (L + 1) < 8 * q + 8 + K := by
    rw [Nat.div_lt_iff_lt_mul (by omega)]
    nlinarith
  nlinarith

/-- **Counting 3-SAT from Theorem 2.3 at space `s / log s`** (paper §8): if Theorem 2.3 holds in bit
form at the space bound `D n = n / (log₂ n + 1) + 1`, the number of satisfying assignments of a
3-CNF formula with `m` clauses is computed (bit `j ≤ 3m` from the encoding of `(φ, j)`) in time
`2^(C · (m / (log₂ m + 1) + 1))` and space `C · (m / (log₂ m + 1) + 1)`: time `2^{O(m/log m)}`. -/
theorem smallBits_nlog (hQ : CubeCountingAt fun n => n / (Nat.log 2 n + 1) + 1) :
    ∃ C, DecidableInTimeAndSpace SmallBitLanguage smallEnc
      (fun a => 2 ^ (C * (a.1.φ.length / (Nat.log 2 a.1.φ.length + 1) + 1)))
      (fun a => C * (a.1.φ.length / (Nat.log 2 a.1.φ.length + 1) + 1)) :=
  smallBits_of_linear hQ
    ⟨32, fun n hn => by rw [Nat.log2_eq_log_two]; have := log_le_div_log hn; omega⟩
    fun K => ⟨K + 9, fun m _ => div_log_linear m K⟩

/-! ### Space `t^{1-ε}` -/

/-- `log₂ n ≤ n^r` for large `n`, for every real `r > 0`. -/
theorem eventually_log_le_rpow {r : ℝ} (hr : 0 < r) :
    ∃ N, ∀ n : ℕ, N ≤ n → (Nat.log 2 n : ℝ) ≤ (n : ℝ) ^ r := by
  have h2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hb := (isLittleO_log_rpow_atTop hr).bound h2
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((tendsto_natCast_atTop_atTop.eventually hb).and (eventually_ge_atTop 1))
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨hle, hn1⟩ := hN n hn
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hpow : ((2 : ℕ) ^ Nat.log 2 n : ℝ) ≤ n := by
    exact_mod_cast Nat.pow_log_le_self 2 (by omega)
  have hlog : (Nat.log 2 n : ℝ) * Real.log 2 ≤ Real.log n := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) (by exact_mod_cast hpow)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hpos.le r)] at hle
  have := hlog.trans ((le_abs_self _).trans hle)
  nlinarith

/-- `D(8m + K) ≤ (K + 9) D(m)` for `D n = ⌊n^r⌋ + 1`, `0 ≤ r ≤ 1`, `m ≥ 1`. -/
theorem floor_rpow_linear {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (K : ℕ) {m : ℕ} (hm : 1 ≤ m) :
    ⌊((8 * m + K : ℕ) : ℝ) ^ r⌋₊ + 1 ≤ (K + 9) * (⌊(m : ℝ) ^ r⌋₊ + 1) := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hc : (1 : ℝ) ≤ 8 + K := by have : (0 : ℝ) ≤ K := K.cast_nonneg; linarith
  have h1 : ((8 * m + K : ℕ) : ℝ) ≤ (8 + K) * m := by
    push_cast
    have : (K : ℝ) ≤ K * m := le_mul_of_one_le_right K.cast_nonneg hm'
    linarith
  have h2 : ((8 * m + K : ℕ) : ℝ) ^ r ≤ (8 + K) * (⌊(m : ℝ) ^ r⌋₊ + 1) := by
    calc ((8 * m + K : ℕ) : ℝ) ^ r ≤ ((8 + K) * m) ^ r :=
          Real.rpow_le_rpow (by positivity) h1 hr0
      _ = (8 + K) ^ r * (m : ℝ) ^ r := Real.mul_rpow (by positivity) (by positivity)
      _ ≤ (8 + K) * (⌊(m : ℝ) ^ r⌋₊ + 1) := by
        have ha : ((8 : ℝ) + K) ^ r ≤ 8 + K := by
          simpa using Real.rpow_le_rpow_of_exponent_le hc hr1
        have hb : (m : ℝ) ^ r ≤ ⌊(m : ℝ) ^ r⌋₊ + 1 := (Nat.lt_floor_add_one _).le
        exact mul_le_mul ha hb (by positivity) (by positivity)
  have h3 : ⌊((8 * m + K : ℕ) : ℝ) ^ r⌋₊ ≤ (8 + K) * (⌊(m : ℝ) ^ r⌋₊ + 1) :=
    Nat.floor_le_of_le (by push_cast at h2 ⊢; exact h2)
  nlinarith

/-- **Counting 3-SAT from Theorem 2.3 at space `s^{1-ε}`** (paper §8): for real `0 ≤ ε < 1`, if
Theorem 2.3 holds in bit form at the space bound `D n = ⌊n^(1-ε)⌋ + 1`, the number of satisfying
assignments of a 3-CNF formula with `m` clauses is computed (bit `j ≤ 3m` from the encoding of
`(φ, j)`) in time `2^(C · (⌊m^(1-ε)⌋ + 1))` and space `C · (⌊m^(1-ε)⌋ + 1)`: time
`2^{O(m^{1-ε})}`. -/
theorem smallBits_rpow {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hQ : CubeCountingAt fun n => ⌊(n : ℝ) ^ (1 - ε)⌋₊ + 1) :
    ∃ C, DecidableInTimeAndSpace SmallBitLanguage smallEnc
      (fun a => 2 ^ (C * (⌊(a.1.φ.length : ℝ) ^ (1 - ε)⌋₊ + 1)))
      (fun a => C * (⌊(a.1.φ.length : ℝ) ^ (1 - ε)⌋₊ + 1)) := by
  obtain ⟨N, hN⟩ := eventually_log_le_rpow (show 0 < 1 - ε by linarith)
  exact smallBits_of_linear hQ
    ⟨N, fun n hn => by rw [Nat.log2_eq_log_two]; have := Nat.le_floor (hN n hn); omega⟩
    fun K => ⟨K + 9, fun m hm => floor_rpow_linear (by linarith) (by linarith) K hm⟩

end Cslib.Complexity.NtimeDspace.Cross.ThreeSat
