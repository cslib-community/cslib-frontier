/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Hierarchy.LazyDiagonal
public import CslibFrontier.Computability.Complexity.Classes.Time
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CslibFrontier.Computability.Complexity.Classes.Hierarchy.LazyDiagonalBounds
import CslibFrontier.Computability.Complexity.Classes.Hierarchy.LazyDiagonalVerifier
import CslibFrontier.Computability.Complexity.Classes.Hierarchy.TimePolylog
import CslibFrontier.Computability.Complexity.Classes.Time.BoundedExists
import CslibFrontier.Computability.Complexity.Classes.Time.Verifier
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Constructible
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.FunPropLists
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.TwoPow
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Frame
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Exponential
import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.BitLength
import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.ResourceBound
import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.WindowedComplexity
import CslibFrontier.Foundations.Data.Nat.LogRpow
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Exponential
import CslibFrontier.Tactic.EncLen

/-!
# A fine nondeterministic exponential time hierarchy by lazy diagonalization

The coarse exponential hierarchy (`Cslib.Complexity.NTIME_two_pow_ssubset_NTIME_two_pow_of_le`)
has an `8 k + 16` gap in the exponent because it runs the quadratic universal simulator. Replacing
the simulator with the `O(t log t)` windowed universal machine
(`Turing.MultiTapeTM.Universal.computableInO_universal_nlogn`), choosing certificates of length
`certLen e m = 2 ^ (m - e * Nat.size (m + 1))` (computed in unary in `O(2 ^ n)` time via
`ComputableInO.unary_two_pow`), and testing the horizon `horizon c P = 2 ^ (P + c)` without
writing it in unary (`Nat.size m ≤ 2 ^ r ↔ Nat.size (Nat.size m - 1) ≤ r`) narrows the gap to a
fixed polynomial factor:

* `Cslib.Complexity.exists_NTIME_two_pow_div_pow_ssubset`: there is an explicit constant `k` such
  that `NTIME (2 ^ n / (n + 1) ^ k) ⊂ NTIME (2 ^ n)` on bit strings, separated by the explicit
  lazy diagonal `Cslib.Complexity.fineExpLazyDiagonal`.
* `Cslib.Complexity.NTIME_two_pow_sub_rpow_ssubset`: for every real `δ > 0` and `c₀ > 0`,
  `NTIME (⌊2 ^ (n - c₀ * n ^ δ)⌋₊) ⊂ NTIME (2 ^ n)` on bit strings.

This is the fine exponential form of the nondeterministic time hierarchy theorem needed by
Williams's `ACC⁰` lower-bound program ([Zak1983]; [Williams2014], Section 3, p. 8). The
polynomial-factor exponent `k` reflects the fixed polynomial overhead of description decoding and
the windowed universal simulator, rather than the sharper `o(2 ^ n / n)` gap of a direct
RAM simulation.

## Main definitions

* `Cslib.Complexity.FineExpLazyDiagonal.certLen`,
  `Cslib.Complexity.FineExpLazyDiagonal.budget`,
  `Cslib.Complexity.FineExpLazyDiagonal.horizon`: parameters of the fine exponential lazy diagonal.
* `Cslib.Complexity.fineExpLazyDiagonal`: the explicit separating language.

## Main results

* `Cslib.Complexity.exists_length_ge_fineExpLazyDiagonal_disagree`: every problem in
  `NTIME (2 ^ n / (n + 1) ^ (e + 1))` differs from `fineExpLazyDiagonal e c` at arbitrarily large
  lengths; `Cslib.Complexity.fineExpLazyDiagonal_notMem_NTIME`: so the diagonal is outside it.
* `Cslib.Complexity.exists_fineExpLazyDiagonal_mem_NTIME`: for all sufficiently large `e` and
  `c` (depending on `e`), `fineExpLazyDiagonal e c ∈ NTIME (2 ^ n)`.
* `Cslib.Complexity.exists_NTIME_two_pow_div_pow_ssubset`:
  `∃ k, NTIME (2 ^ n / (n + 1) ^ k) ⊂ NTIME (2 ^ n)`.
* `Cslib.Complexity.NTIME_two_pow_sub_rpow_ssubset`:
  `NTIME (⌊2 ^ (n - c₀ * n ^ δ)⌋₊) ⊂ NTIME (2 ^ n)` for all `δ > 0` and `c₀ > 0`.
* `Cslib.Complexity.exists_mem_NTIME_two_pow_forall_exists_length_ge`: the same separation at
  arbitrarily large lengths, robust under changes on finitely many lengths.
* `Cslib.Complexity.eventually_floor_two_pow_sub_rpow_le`: subexponential savings eventually beat
  every polynomial factor.

## References

* [S. Žák, *A Turing machine time hierarchy*][Zak1983]
* [R. Williams, *Non-uniform ACC Circuit Lower Bounds*, July 31, 2012 version, Section 3,
  p. 8][Williams2014]
-/

public section

namespace Cslib.Complexity

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.Universal Filter

namespace FineExpLazyDiagonal

/-- Certificate length on words of length `m`: `2 ^ (m - e * Nat.size (m + 1))`, which is
`Θ(2 ^ m / (m + 1) ^ e)` and an exact power of two so it can be constructed in unary in time
`O(2 ^ (m - 1))`. -/
@[expose] def certLen (e m : ℕ) : ℕ :=
  2 ^ (m - e * Nat.size (m + 1))

/-- Step budget on input `y` (independent of the certificate `v`): when `|v| = certLen e |y|`, this
equals `((encPair encBits encBits (y, v)).length + 1) * (Nat.size (|y| + 1) + 1)`, which
eventually dominates every linear multiple of the pair length while remaining computable in
polynomial time in `|y|` alone. -/
@[expose] def budget (e : ℕ) (y _ : List Bool) : ℕ :=
  (2 * y.length + 2 + certLen e y.length) * (Nat.size (y.length + 1) + 1)

/-- Horizon of the interval starting at length `P`: `2 ^ (P + c)`. -/
@[expose] def horizon (c P : ℕ) : ℕ :=
  2 ^ (P + c)

end FineExpLazyDiagonal

open FineExpLazyDiagonal

/-- **The fine exponential lazy diagonal language** with parameters `e` and `c`: the words `x`
with an accepted certificate of length `2 ^ ((x.length + 1) - e * Nat.size (x.length + 2))`. -/
@[expose] def fineExpLazyDiagonal (e c : ℕ) : Set (List Bool) :=
  Diagonal.lazyLanguage (budget e) (certLen e) (horizon c)

/-! ### Lower bound: outside `NTIME (2 ^ n / (n + 1) ^ (e + 1))` -/

private theorem two_pow_size_succ_le (m : ℕ) : 2 ^ Nat.size (m + 1) ≤ 2 * (m + 1) := by
  have hpos : 0 < Nat.size (m + 1) := Nat.size_pos.2 (Nat.succ_pos m)
  have hlt : 2 ^ (Nat.size (m + 1) - 1) ≤ m + 1 := Nat.lt_size.mp (by omega)
  have heq : 2 ^ Nat.size (m + 1) = 2 * 2 ^ (Nat.size (m + 1) - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  omega

private theorem exists_le_fineCertLen (e c₀ : ℕ) :
    ∃ M, ∀ m, M ≤ m → c₀ * (2 ^ m / (m + 1) ^ (e + 1)) + c₀ ≤ certLen e m := by
  obtain ⟨M₁, hM₁⟩ := eventually_atTop.mp
    (PolynomiallyBounded.eventually_lt_two_pow
      (f := fun m => 2 * (c₀ + 1) * 2 ^ e * (m + 1) ^ e) (by fun_prop))
  refine ⟨max M₁ (2 * (c₀ + 1) * 2 ^ e), fun m hm => ?_⟩
  have hm₁ : M₁ ≤ m := (le_max_left _ _).trans hm
  have hm₂ : 2 * (c₀ + 1) * 2 ^ e ≤ m := (le_max_right _ _).trans hm
  have hbig : 2 * (c₀ + 1) * 2 ^ e * (m + 1) ^ e < 2 ^ m := hM₁ m hm₁
  have hpow_sz : 2 ^ (e * Nat.size (m + 1)) ≤ 2 ^ e * (m + 1) ^ e := by
    rw [mul_comm e, pow_mul, ← mul_pow]
    exact Nat.pow_le_pow_left (two_pow_size_succ_le m) e
  have hsub : e * Nat.size (m + 1) ≤ m := by
    have hlt : 2 ^ (e * Nat.size (m + 1)) < 2 ^ m := by
      have h1 : 1 ≤ 2 * (c₀ + 1) := by omega
      have h2 : 2 ^ e * (m + 1) ^ e ≤ 2 * (c₀ + 1) * 2 ^ e * (m + 1) ^ e := by
        rw [mul_assoc (2 * (c₀ + 1))]
        exact Nat.le_mul_of_pos_left _ h1
      exact lt_of_le_of_lt (hpow_sz.trans h2) hbig
    exact (Nat.pow_lt_pow_iff_right Nat.one_lt_two).1 hlt |>.le
  have hdiv : 2 ^ m / (m + 1) ^ (e + 1) * (m + 1) ^ (e + 1) ≤ 2 ^ m :=
    Nat.div_mul_le_self _ _
  have hterm1 : 2 * (c₀ * (2 ^ m / (m + 1) ^ (e + 1)) * (2 ^ e * (m + 1) ^ e)) ≤ 2 ^ m := by
    have hcoeff : 2 * c₀ * 2 ^ e ≤ m + 1 := by
      have : 2 * c₀ * 2 ^ e ≤ 2 * (c₀ + 1) * 2 ^ e :=
        Nat.mul_le_mul_right _ (by omega)
      omega
    calc 2 * (c₀ * (2 ^ m / (m + 1) ^ (e + 1)) * (2 ^ e * (m + 1) ^ e))
        = (2 * c₀ * 2 ^ e) * ((2 ^ m / (m + 1) ^ (e + 1)) * (m + 1) ^ e) := by ring
      _ ≤ (m + 1) * ((2 ^ m / (m + 1) ^ (e + 1)) * (m + 1) ^ e) :=
          Nat.mul_le_mul_right _ hcoeff
      _ = 2 ^ m / (m + 1) ^ (e + 1) * (m + 1) ^ (e + 1) := by
          rw [pow_succ]; ring
      _ ≤ 2 ^ m := hdiv
  have hterm2 : 2 * (c₀ * (2 ^ e * (m + 1) ^ e)) ≤ 2 ^ m := by
    have hle : 2 * (c₀ * (2 ^ e * (m + 1) ^ e)) ≤ 2 * (c₀ + 1) * 2 ^ e * (m + 1) ^ e := by
      have : 2 * c₀ ≤ 2 * (c₀ + 1) := by omega
      calc 2 * (c₀ * (2 ^ e * (m + 1) ^ e)) = (2 * c₀) * (2 ^ e * (m + 1) ^ e) := by ring
        _ ≤ (2 * (c₀ + 1)) * (2 ^ e * (m + 1) ^ e) := Nat.mul_le_mul_right _ this
        _ = 2 * (c₀ + 1) * 2 ^ e * (m + 1) ^ e := by ring
    exact hle.trans hbig.le
  have hsum : (c₀ * (2 ^ m / (m + 1) ^ (e + 1)) + c₀) * (2 ^ e * (m + 1) ^ e) ≤ 2 ^ m := by
    have : 2 * ((c₀ * (2 ^ m / (m + 1) ^ (e + 1)) + c₀) * (2 ^ e * (m + 1) ^ e)) =
        2 * (c₀ * (2 ^ m / (m + 1) ^ (e + 1)) * (2 ^ e * (m + 1) ^ e)) +
          2 * (c₀ * (2 ^ e * (m + 1) ^ e)) := by ring
    omega
  have hmul : (c₀ * (2 ^ m / (m + 1) ^ (e + 1)) + c₀) * 2 ^ (e * Nat.size (m + 1)) ≤
      certLen e m * 2 ^ (e * Nat.size (m + 1)) := by
    rw [certLen, ← pow_add, Nat.sub_add_cancel hsub]
    exact (Nat.mul_le_mul_left _ hpow_sz).trans hsum
  exact Nat.le_of_mul_le_mul_right hmul (Nat.two_pow_pos _)

/-- **Every problem in `NTIME (2 ^ n / (n + 1) ^ (e + 1))` differs from the fine exponential lazy
diagonal at arbitrarily large lengths**
(`Cslib.Complexity.Diagonal.exists_length_ge_lazyLanguage_disagree`). -/
theorem exists_length_ge_fineExpLazyDiagonal_disagree (e c : ℕ) {B : Set (List Bool)}
    (hB : B ∈ NTIME encBits fun n => 2 ^ n / (n + 1) ^ (e + 1)) (N₀ : ℕ) :
    ∃ y : List Bool, N₀ ≤ y.length ∧ ¬ (y ∈ fineExpLazyDiagonal e c ↔ y ∈ B) :=
  Diagonal.exists_length_ge_lazyLanguage_disagree (exists_le_fineCertLen e)
    (fun c₂ => ⟨2 ^ c₂, fun y v hy hv => by
      have hsz : c₂ < Nat.size (y.length + 1) := Nat.lt_size.mpr (by omega)
      have hlen : (encPair encBits encBits (y, v)).length + 1 =
          2 * y.length + 2 + certLen e y.length := by
        simp only [length_encPair, encBits_apply, hv]; omega
      rw [hlen, budget, mul_comm c₂]
      exact Nat.mul_le_mul_left _ (by omega)⟩)
    (fun P => by
      have h1 : P + 1 ≤ 2 ^ (P + c) :=
        (Nat.lt_two_pow_self (n := P)).trans_le
          (Nat.pow_le_pow_right Nat.one_lt_two.le (Nat.le_add_right P c))
      exact h1.trans_lt Nat.lt_two_pow_self) hB N₀

/-- **The fine exponential lazy diagonal is outside `NTIME (2 ^ n / (n + 1) ^ (e + 1))`**
(`Cslib.Complexity.Diagonal.lazyLanguage_notMem_NTIME`). -/
theorem fineExpLazyDiagonal_notMem_NTIME (e c : ℕ) :
    fineExpLazyDiagonal e c ∉ NTIME encBits fun n => 2 ^ n / (n + 1) ^ (e + 1) := fun hD =>
  let ⟨_, _, hy⟩ := exists_length_ge_fineExpLazyDiagonal_disagree e c hD 0
  hy Iff.rfl

/-! ### Upper bound: inside `NTIME (2 ^ n)` via the `O(t log t)` universal machine -/

private theorem size_le_two_pow_iff (m r : ℕ) :
    Nat.size m ≤ 2 ^ r ↔ Nat.size (Nat.size m - 1) ≤ r := by
  conv_rhs => rw [Nat.size_le]
  have hpos : 0 < 2 ^ r := Nat.two_pow_pos r
  omega

/-- The unary exponent `m - e * Nat.size (m + 1)` is polynomial-time from a bit string of length
`m` (or `m - 1`). -/
private theorem computableInPolyTime_certExp (e shift : ℕ) :
    ComputableInPolyTime
      (fun x : List Bool => (x.length + shift) - e * Nat.size (x.length + shift + 1))
      encBits encUnary := by
  have hlen : ComputableInPolyTime (fun x : List Bool => x.length + shift) encBits encUnary := by
    fun_prop
  have hsz : ComputableInPolyTime (fun x : List Bool => Nat.size (x.length + shift + 1))
      encBits encUnary :=
    ComputableInPolyTime.binary_size.comp (ComputableInPolyTime.unary_to_binary.comp (by fun_prop))
  fun_prop

/-- The binary step budget `budget e y _` is polynomial-time in `y` alone. -/
private theorem computableInPolyTime_budgetOfY (e : ℕ) :
    ComputableInPolyTime (fun y : List Bool => budget e y []) encBits encNat := by
  have hexp : ComputableInPolyTime (fun y : List Bool => y.length - e * Nat.size (y.length + 1))
      encBits encUnary := by
    simpa only [Nat.add_zero] using computableInPolyTime_certExp e 0
  have hcert : ComputableInPolyTime (fun y : List Bool => certLen e y.length) encBits encNat :=
    ComputableInPolyTime.binary_two_pow.comp hexp
  have hlin : ComputableInPolyTime (fun y : List Bool => 2 * y.length + 2) encBits encNat :=
    ComputableInPolyTime.unary_to_binary.comp (by fun_prop)
  have hsz0 : ComputableInPolyTime (fun y : List Bool => Nat.size (y.length + 1))
      encBits encUnary :=
    ComputableInPolyTime.binary_size.comp
      (ComputableInPolyTime.unary_to_binary.comp (by fun_prop))
  have hsz : ComputableInPolyTime (fun y : List Bool => Nat.size (y.length + 1) + 1)
      encBits encNat :=
    ComputableInPolyTime.unary_to_binary.comp (by fun_prop)
  unfold budget
  exact ComputableInPolyTime.binary_mul'
    (ComputableInPolyTime.binary_add' hlin hcert) hsz

/-- Horizon comparison `Nat.size (|x| + shift) ≤ 2 ^ (2 * |unframe x| + 1 + c)` is polynomial-time
in `x` alone, without ever materializing the exponential horizon in unary. -/
private theorem computableInPolyTime_horizonTest (c shift : ℕ) :
    ComputableInPolyTime (fun x : List Bool =>
      decide (Nat.size (x.length + shift) ≤ horizon c (2 * (unframe x).length + 1)))
      encBits encBool := by
  have hs1 : ComputableInPolyTime (fun x : List Bool => Nat.size (x.length + shift))
      encBits encUnary :=
    ComputableInPolyTime.binary_size.comp
      (ComputableInPolyTime.unary_to_binary.comp (by fun_prop))
  have hs2 : ComputableInPolyTime (fun x : List Bool => Nat.size (Nat.size (x.length + shift) - 1))
      encBits encUnary :=
    ComputableInPolyTime.binary_size.comp
      (ComputableInPolyTime.unary_to_binary.comp (by fun_prop))
  have hr : ComputableInPolyTime (fun x : List Bool => 2 * (unframe x).length + 1 + c)
      encBits encUnary := by fun_prop
  exact (ComputableInPolyTime.unary_le.comp (hs2.prod hr)).of_enc_eq fun x => by
    simp only [horizon, Function.comp_apply, encBool_apply, List.cons.injEq, and_true]
    exact decide_eq_decide.mpr
      (size_le_two_pow_iff (x.length + shift) (2 * (unframe x).length + 1 + c))

/-- For `e ≥ 1`, `(n + 1 - e * Nat.size (n + 2) + 1) * certLen e (n + 1) ≤ 2 * 2 ^ n`. -/
private theorem certExp_mul_certLen_le {e : ℕ} (he : 1 ≤ e) (n : ℕ) :
    ((n + 1) - e * Nat.size (n + 2) + 1) * certLen e (n + 1) ≤ 2 * 2 ^ n := by
  unfold certLen
  rw [show n + 1 + 1 = n + 2 from rfl]
  by_cases h : e * Nat.size (n + 2) ≤ n + 1
  · have h1 : (n + 1) - e * Nat.size (n + 2) + 1 ≤ 2 ^ Nat.size (n + 2) :=
      (by omega : (n + 1) - e * Nat.size (n + 2) + 1 ≤ n + 2).trans (Nat.lt_size_self _).le
    have h2 : Nat.size (n + 2) + ((n + 1) - e * Nat.size (n + 2)) ≤ n + 1 := by
      have : Nat.size (n + 2) ≤ e * Nat.size (n + 2) := Nat.le_mul_of_pos_left _ he
      omega
    calc ((n + 1) - e * Nat.size (n + 2) + 1) * 2 ^ ((n + 1) - e * Nat.size (n + 2))
        ≤ 2 ^ Nat.size (n + 2) * 2 ^ ((n + 1) - e * Nat.size (n + 2)) :=
          Nat.mul_le_mul_right _ h1
      _ = 2 ^ (Nat.size (n + 2) + ((n + 1) - e * Nat.size (n + 2))) := (pow_add 2 _ _).symm
      _ ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right Nat.one_lt_two.le h2
      _ = 2 * 2 ^ n := by rw [pow_succ']
  · have h0 : (n + 1) - e * Nat.size (n + 2) = 0 := by omega
    rw [h0]
    simp only [zero_add, pow_zero, mul_one]
    have := Nat.one_le_two_pow (n := n)
    omega

/-- For `e ≥ d`, `(n + 2) ^ d * certLen e (n + 1) ≤ (n + 2) ^ d + 2 * 2 ^ n`. -/
private theorem pow_mul_certLen_le {e d : ℕ} (hed : d ≤ e) (n : ℕ) :
    (n + 2) ^ d * certLen e (n + 1) ≤ (n + 2) ^ d + 2 * 2 ^ n := by
  unfold certLen
  rw [show n + 1 + 1 = n + 2 from rfl]
  by_cases h : e * Nat.size (n + 2) ≤ n + 1
  · have h1 : (n + 2) ^ d ≤ 2 ^ (d * Nat.size (n + 2)) := by
      rw [mul_comm d, pow_mul]
      exact Nat.pow_le_pow_left (Nat.lt_size_self (n + 2)).le d
    have h2 : d * Nat.size (n + 2) + ((n + 1) - e * Nat.size (n + 2)) ≤ n + 1 := by
      have : d * Nat.size (n + 2) ≤ e * Nat.size (n + 2) := Nat.mul_le_mul_right _ hed
      omega
    have h3 : (n + 2) ^ d * 2 ^ ((n + 1) - e * Nat.size (n + 2)) ≤ 2 * 2 ^ n := by
      calc (n + 2) ^ d * 2 ^ ((n + 1) - e * Nat.size (n + 2))
          ≤ 2 ^ (d * Nat.size (n + 2)) * 2 ^ ((n + 1) - e * Nat.size (n + 2)) :=
            Nat.mul_le_mul_right _ h1
        _ = 2 ^ (d * Nat.size (n + 2) + ((n + 1) - e * Nat.size (n + 2))) := (pow_add 2 _ _).symm
        _ ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right Nat.one_lt_two.le h2
        _ = 2 * 2 ^ n := by rw [pow_succ']
    omega
  · have h0 : (n + 1) - e * Nat.size (n + 2) = 0 := by omega
    rw [h0, pow_zero, mul_one]
    exact Nat.le_add_right _ _

/-- Pure arithmetic kernel bounding the `O(t log t)` universal simulation cost. -/
private theorem fineAccepts_arith (ce cO N A B D dlen Mlen Nl Bl Y E : ℕ)
    (hDlen : dlen ≤ ce * D) (hM : Mlen ≤ 1) (hNl : Nl ≤ 3 * N) (hBl : Bl ≤ Y)
    (hYpos : 1 ≤ Y)
    (hE : E ≤ cO * (N + A + (N + (N + (2 * N + B))) +
      ((2 * dlen + 1 + (2 * Nl + 1 + Bl)) + (dlen + Mlen + 2) ^ 6 * Y) + 1)) :
    (N + A + (N + (N + (2 * N + B))) +
      ((2 * dlen + 1 + (2 * Nl + 1 + Bl)) + (dlen + Mlen + 2) ^ 6 * Y)) + E + 1 ≤
      (34 * (cO + 1) * (ce + 3) ^ 6 + 64) * (N + A + B + (D + 1) ^ 6 * Y + 1) := by
  set W := N + A + B + (D + 1) ^ 6 * Y
  have hDM : (dlen + Mlen + 2) ^ 6 ≤ (ce + 3) ^ 6 * (D + 1) ^ 6 := by
    rw [← mul_pow]
    refine Nat.pow_le_pow_left ?_ 6
    have h1 : ce * D ≤ ce * (D + 1) := Nat.mul_le_mul_left _ (Nat.le_succ D)
    have h2 : 3 ≤ 3 * (D + 1) := by omega
    have : (ce + 3) * (D + 1) = ce * (D + 1) + 3 * (D + 1) := by ring
    omega
  have hUterm : (dlen + Mlen + 2) ^ 6 * Y ≤ (ce + 3) ^ 6 * ((D + 1) ^ 6 * Y) := by
    rw [← mul_assoc]
    exact Nat.mul_le_mul_right Y hDM
  have hBl' : Bl ≤ (D + 1) ^ 6 * Y :=
    hBl.trans (Nat.le_mul_of_pos_left _ (Nat.pow_pos (Nat.succ_pos _)))
  have hDle : dlen ≤ ce * ((D + 1) ^ 6 * Y) := by
    have hD6 : D ≤ (D + 1) ^ 6 := (Nat.le_succ D).trans (Nat.le_self_pow (by decide) _)
    exact hDlen.trans (Nat.mul_le_mul_left ce (hD6.trans (Nat.le_mul_of_pos_right _ hYpos)))
  have hCore : N + A + (N + (N + (2 * N + B))) +
      ((2 * dlen + 1 + (2 * Nl + 1 + Bl)) + (dlen + Mlen + 2) ^ 6 * Y) ≤
      (18 + 2 * ce + (ce + 3) ^ 6) * (W + 1) := by
    have hce1 : ce * ((D + 1) ^ 6 * Y) ≤ ce * (W + 1) := Nat.mul_le_mul_left ce (by omega)
    have hce6 : (ce + 3) ^ 6 * ((D + 1) ^ 6 * Y) ≤ (ce + 3) ^ 6 * (W + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have heq : (18 + 2 * ce + (ce + 3) ^ 6) * (W + 1) =
        18 * (W + 1) + 2 * (ce * (W + 1)) + (ce + 3) ^ 6 * (W + 1) := by ring
    omega
  have hce_le : 18 + 2 * ce + (ce + 3) ^ 6 ≤ 21 * (ce + 3) ^ 6 := by
    have h1 : 1 ≤ (ce + 3) ^ 6 := Nat.one_le_pow _ _ (by omega)
    have h2 : ce ≤ (ce + 3) ^ 6 := (by omega : ce ≤ ce + 3).trans (Nat.le_self_pow (by decide) _)
    omega
  have hCore2 : N + A + (N + (N + (2 * N + B))) +
      ((2 * dlen + 1 + (2 * Nl + 1 + Bl)) + (dlen + Mlen + 2) ^ 6 * Y) ≤
      21 * (ce + 3) ^ 6 * (W + 1) :=
    hCore.trans (Nat.mul_le_mul_right _ hce_le)
  have hE2 : E ≤ cO * (21 * (ce + 3) ^ 6 * (W + 1) + 1) :=
    hE.trans (Nat.mul_le_mul_left cO (by omega))
  set U := (ce + 3) ^ 6 * (W + 1)
  have hCore3 : N + A + (N + (N + (2 * N + B))) +
      ((2 * dlen + 1 + (2 * Nl + 1 + Bl)) + (dlen + Mlen + 2) ^ 6 * Y) ≤ 21 * U := by
    rwa [show 21 * (ce + 3) ^ 6 * (W + 1) = 21 * U by dsimp only [U]; ring] at hCore2
  have h1 : cO ≤ cO * (W + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos W)
  have h2 : 1 ≤ (ce + 3) ^ 6 := Nat.one_le_pow _ _ (by omega)
  have h3 : cO * (21 * (ce + 3) ^ 6 * (W + 1) + 1) = 21 * (cO * U) + cO := by
    dsimp only [U]; ring
  have h4 : (34 * (cO + 1) * (ce + 3) ^ 6 + 64) * (W + 1) =
      34 * (cO * U) + 34 * U + 64 * (W + 1) := by dsimp only [U]; ring
  have h5 : cO * (W + 1) ≤ cO * U := by
    dsimp only [U]
    rw [← mul_assoc, mul_comm cO ((ce + 3) ^ 6), mul_assoc]
    exact Nat.le_mul_of_pos_left _ h2
  omega

-- Compose through the named decoder and windowed simulator without unfolding them during `omega`.
attribute [local irreducible] ComputableInO Universal.decodeDesc Universal.eDesc in
/-- **Fast `lazyAccepts` simulation** via the `O(t log t)` windowed universal machine: on input
`(code, y, v)`, the simulation runs in time `O(|enc| + (|code| + 1)^dd + (|y| + 1)^db +
((|code| + 1)^ed + 1)^6 * (budget e y v + 1) * (log₂ (budget e y v + 1) + 1))`, with no quadratic
dependence on `|v|`. -/
private theorem exists_computableInO_fineAccepts :
    ∃ (dd ed : ℕ), ∀ e : ℕ, ∃ (db : ℕ),
      ComputableInO
        (fun q : List Bool × List Bool × List Bool =>
          Diagonal.lazyAccepts (budget e) q.1 q.2.1 q.2.2)
        Diagonal.encLazyAcceptsInput encBool
        (fun q => (Diagonal.encLazyAcceptsInput q).length + (q.1.length + 1) ^ dd +
          (q.2.1.length + 1) ^ db +
          ((q.1.length + 1) ^ ed + 1) ^ 6 *
            ((budget e q.2.1 q.2.2 + 1) * (Nat.log 2 (budget e q.2.1 q.2.2 + 1) + 1)))
        (fun q => (Diagonal.encLazyAcceptsInput q).length + (q.1.length + 1) ^ dd +
          (q.2.1.length + 1) ^ db +
          ((q.1.length + 1) ^ ed + 1) ^ 6 *
            ((budget e q.2.1 q.2.2 + 1) * (Nat.log 2 (budget e q.2.1 q.2.2 + 1) + 1))) := by
  obtain ⟨dd, ed, hdec⟩ := exists_computableInDegree_decodeDesc
  obtain ⟨ce, hce⟩ := hdec.2
  refine ⟨dd, ed, fun e => ?_⟩
  obtain ⟨db, _, hbud⟩ := (computableInPolyTime_budgetOfY e).exists_degree
  refine ⟨db, ?_⟩
  set enc := Diagonal.encLazyAcceptsInput
  have hdesc := hdec.inO.comp (ComputableInO.fst encBits (encPair encBits encBits))
  have hword : ComputableInO (fun q : List Bool × List Bool × List Bool => frame q.2.1 ++ q.2.2)
      enc encBits (fun q => (enc q).length) (fun q => (enc q).length) :=
    (ComputableInO.snd encBits (encPair encBits encBits)).of_enc_eq fun _ => rfl
  have hsym := Universal.computableInO_map_eBit.comp hword
  have hy : ComputableInO (fun q : List Bool × List Bool × List Bool => q.2.1) enc encBits
      (fun q => 2 * (enc q).length) (fun q => 2 * (enc q).length) := by
    have h1 := (ComputableInO.fst encBits encBits).comp
      (ComputableInO.snd encBits (encPair encBits encBits))
    refine h1.mono 2 (fun q => ?_) (fun q => ?_)
    all_goals
      have hle := length_le_encPair_right encBits (encPair encBits encBits) q
      dsimp only [Function.comp_apply, enc, Diagonal.encLazyAcceptsInput] at hle ⊢
      omega
  have hclock : ComputableInO (fun q : List Bool × List Bool × List Bool => budget e q.2.1 q.2.2)
      enc encNat
      (fun q => 2 * (enc q).length + (q.2.1.length + 1) ^ db)
      (fun q => 2 * (enc q).length + (q.2.1.length + 1) ^ db) :=
    (hbud.inO.comp hy).of_enc_eq fun _ => rfl
  have hpre := hdesc.prod (hsym.prod hclock)
  have hU := computableInO_universal_nlogn.comp hpre
  have hv := Diagonal.computableInO_verdict_linear.comp hU
  have hnot := (ComputableInDegree.of_finite (encIn := encBool) (encMid := encBool)
    (fun b : Bool => !b)).inO_one.comp hv
  obtain ⟨cO, hcO⟩ := hU.length_le
  refine (hnot.mono (34 * (cO + 1) * (ce + 3) ^ 6 + 64) (fun q => ?_) (fun q => ?_)).of_enc_eq
    fun _ => rfl
  all_goals
    have hDlen : descLen (decodeDesc q.1) ≤ ce * (q.1.length + 1) ^ ed := by
      simpa only [descLen, encBits_apply] using hce q.1
    have hM : listMax id ((frame q.2.1 ++ q.2.2).map eBit) ≤ 1 := by
      refine listMax_le fun a ha => ?_
      obtain ⟨b, -, rfl⟩ := List.mem_map.mp ha
      cases b <;> decide
    have hWle : (frame q.2.1 ++ q.2.2).length ≤ (enc q).length := by
      simpa only [enc, Diagonal.encLazyAcceptsInput, encPair_apply, encBits_apply] using
        length_le_encPair_right encBits (encPair encBits encBits) q
    have hNl : ((encList encUnary) ((frame q.2.1 ++ q.2.2).map eBit)).length ≤
        3 * (enc q).length := by
      have := length_encList_map_eBit_le (frame q.2.1 ++ q.2.2); omega
    have hBl : (encNat (budget e q.2.1 q.2.2)).length ≤
        (budget e q.2.1 q.2.2 + 1) * (Nat.log 2 (budget e q.2.1 q.2.2 + 1) + 1) :=
      (Universal.length_encNat_le _).trans
        ((Nat.le_succ _).trans (Nat.le_mul_of_pos_right _ (Nat.succ_pos _)))
    have heIn_eq :
        (eIn (decodeDesc q.1, (frame q.2.1 ++ q.2.2).map eBit, budget e q.2.1 q.2.2)).length =
        2 * descLen (decodeDesc q.1) + 1 +
          (2 * ((encList encUnary) ((frame q.2.1 ++ q.2.2).map eBit)).length + 1 +
            (encNat (budget e q.2.1 q.2.2)).length) := by
      simp only [eIn, length_encPair, descLen]
    have hO := hcO q
    simp only [Function.comp_apply, encBits_apply, encBool_apply, List.length_singleton] at hO ⊢
    dsimp only [enc, Diagonal.encLazyAcceptsInput] at hO hWle hNl ⊢
    rw [heIn_eq] at hO ⊢
    have hE : (eOut (universal (decodeDesc q.1, (frame q.2.1 ++ q.2.2).map eBit,
        budget e q.2.1 q.2.2))).length ≤
        cO * ((encPair encBits (encPair encBits encBits) q).length + (q.1.length + 1) ^ dd +
          ((encPair encBits (encPair encBits encBits) q).length +
            ((encPair encBits (encPair encBits encBits) q).length +
              (2 * (encPair encBits (encPair encBits encBits) q).length +
                (q.2.1.length + 1) ^ db))) +
          ((2 * descLen (decodeDesc q.1) + 1 +
              (2 * ((encList encUnary) ((frame q.2.1 ++ q.2.2).map eBit)).length + 1 +
                (encNat (budget e q.2.1 q.2.2)).length)) +
            (descLen (decodeDesc q.1) + listMax id ((frame q.2.1 ++ q.2.2).map eBit) + 2) ^ 6 *
              ((budget e q.2.1 q.2.2 + 1) * (Nat.log 2 (budget e q.2.1 q.2.2 + 1) + 1))) + 1) :=
      hO.trans (Nat.mul_le_mul_left cO (by omega))
    have hArith := fineAccepts_arith ce cO (encPair encBits (encPair encBits encBits) q).length
      ((q.1.length + 1) ^ dd) ((q.2.1.length + 1) ^ db) ((q.1.length + 1) ^ ed)
      (descLen (decodeDesc q.1)) (listMax id ((frame q.2.1 ++ q.2.2).map eBit))
      ((encList encUnary) ((frame q.2.1 ++ q.2.2).map eBit)).length
      (encNat (budget e q.2.1 q.2.2)).length
      ((budget e q.2.1 q.2.2 + 1) * (Nat.log 2 (budget e q.2.1 q.2.2 + 1) + 1))
      (eOut (universal (decodeDesc q.1, (frame q.2.1 ++ q.2.2).map eBit,
        budget e q.2.1 q.2.2))).length
      hDlen hM hNl hBl (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)) hE
    omega

/-- Capped step budget polynomial in `((code, y), u)` (and equal to `budget e y _` when
`u = certLen e |y|`). -/
private def capBudget (e : ℕ) (p : ((List Bool × List Bool) × ℕ) × List Bool) : ℕ :=
  min (budget e p.1.1.2 [])
    ((2 * p.1.1.2.length + 2 + p.1.2) * (Nat.size (p.1.1.2.length + 1) + 1))

/-- Capped acceptance test for brute-force search at the end of an interval. -/
private def capTest (e : ℕ) (p : ((List Bool × List Bool) × ℕ) × List Bool) : Bool :=
  !Diagonal.verdict
    (universal (decodeDesc p.1.1.1, (frame p.1.1.2 ++ p.2).map eBit, capBudget e p))

private theorem computableInPolyTime_capBudget (e : ℕ) :
    ComputableInPolyTime (capBudget e)
      (encPair (encPair (encPair encBits encBits) encUnary) encBits) encNat := by
  set encB := encPair (encPair encBits encBits) encUnary
  have hy : ComputableInPolyTime (fun p : ((List Bool × List Bool) × ℕ) × List Bool => p.1.1.2)
      (encPair encB encBits) encBits := by fun_prop
  have hu : ComputableInPolyTime (fun p : ((List Bool × List Bool) × ℕ) × List Bool => p.1.2)
      (encPair encB encBits) encUnary := by fun_prop
  have hb1 : ComputableInPolyTime (fun p : ((List Bool × List Bool) × ℕ) × List Bool =>
      budget e p.1.1.2 []) (encPair encB encBits) encNat :=
    (computableInPolyTime_budgetOfY e).comp hy
  have hsz0 : ComputableInPolyTime (fun p : ((List Bool × List Bool) × ℕ) × List Bool =>
      Nat.size (p.1.1.2.length + 1)) (encPair encB encBits) encUnary :=
    ComputableInPolyTime.binary_size.comp
      (ComputableInPolyTime.unary_to_binary.comp (by fun_prop))
  have hb2 : ComputableInPolyTime (fun p : ((List Bool × List Bool) × ℕ) × List Bool =>
      (2 * p.1.1.2.length + 2 + p.1.2) * (Nat.size (p.1.1.2.length + 1) + 1))
      (encPair encB encBits) encNat :=
    ComputableInPolyTime.unary_to_binary.comp (by fun_prop)
  have hle := ComputableInPolyTime.binary_le' hb1 hb2
  exact (hle.ite hb1 hb2).of_enc_eq fun p => by
    dsimp only [capBudget]
    split_ifs with h
    · rw [Nat.min_eq_left (of_decide_eq_true h)]
    · rw [Nat.min_eq_right (Nat.le_of_not_le (of_decide_eq_false (Bool.eq_false_iff.2 h)))]

attribute [local irreducible] ComputableInO Universal.decodeDesc Universal.eDesc in
private theorem computableInPolyTime_capTest (e : ℕ) :
    ComputableInPolyTime (capTest e)
      (encPair (encPair (encPair encBits encBits) encUnary) encBits) encBool := by
  set encQ := encPair encBits encBits
  set encB := encPair encQ encUnary
  obtain ⟨_, _, hdec⟩ := exists_computableInDegree_decodeDesc
  have hdesc : ComputableInPolyTime (fun p : ((List Bool × List Bool) × ℕ) × List Bool =>
      decodeDesc p.1.1.1) (encPair encB encBits) eDesc :=
    hdec.computableInPolyTime.comp (by fun_prop)
  have hword : ComputableInPolyTime (fun p : ((List Bool × List Bool) × ℕ) × List Bool =>
      frame p.1.1.2 ++ p.2) (encPair encB encBits) encBits := by
    have h1 : ComputableInPolyTime (fun p : ((List Bool × List Bool) × ℕ) × List Bool =>
        (p.1.1.2, p.2)) (encPair encB encBits) (encPair encBits encBits) := by fun_prop
    exact h1.of_enc_eq fun _ => rfl
  have hsym : ComputableInPolyTime (fun p : ((List Bool × List Bool) × ℕ) × List Bool =>
      (frame p.1.1.2 ++ p.2).map eBit) (encPair encB encBits) (encList encUnary) :=
    (Universal.computableInO_map_eBit.computableInPolyTime
      (PolyBounded.of_forall_le 1 1 fun _ => by simp)
      (PolyBounded.of_forall_le 1 1 fun _ => by simp)).comp hword
  have hpre := hdesc.prod (hsym.prod (computableInPolyTime_capBudget e))
  obtain ⟨Tp, Sp, hTp, hSp, hpreO⟩ := hpre.exists_computableInO
  have hU := computableInO_universal_polynomialBound.comp hpreO
  obtain ⟨_, dI, hcI⟩ := hpre.exists_degree
  obtain ⟨cL, hlen⟩ := hcI.2
  have hIpoly : PolyBounded (fun p => (encPair encB encBits p).length)
      (fun p => (eIn (decodeDesc p.1.1.1, (frame p.1.1.2 ++ p.2).map eBit,
        capBudget e p)).length + 1) :=
    PolyBounded.of_forall_le (cL + 1) dI fun p => by
      have h := hlen p
      have h1 : 1 ≤ ((encPair encB encBits p).length + 1) ^ dI :=
        Nat.one_le_pow _ _ (Nat.succ_pos _)
      dsimp only [eIn] at h ⊢
      have : (cL + 1) * ((encPair encB encBits p).length + 1) ^ dI =
          cL * ((encPair encB encBits p).length + 1) ^ dI +
            ((encPair encB encBits p).length + 1) ^ dI := by ring
      omega
  have hBpoly : PolyBounded (fun p => (encPair encB encBits p).length)
      (fun p => capBudget e p + 1) :=
    PolyBounded.of_forall_le 12 2 fun p => by
      have hy : p.1.1.2.length ≤ (encPair encB encBits p).length := by enc_len [encB, encQ]
      have hu : p.1.2 ≤ (encPair encB encBits p).length := by enc_len [encB, encQ]
      have hsz : Nat.size (p.1.1.2.length + 1) ≤ p.1.1.2.length + 1 :=
        Nat.size_le.2 Nat.lt_two_pow_self
      set n := (encPair encB encBits p).length
      have h1 : capBudget e p ≤ (3 * (n + 1)) * (2 * (n + 1)) :=
        (Nat.min_le_right _ _).trans (Nat.mul_le_mul (by omega) (by omega))
      have h2 : (3 * (n + 1)) * (2 * (n + 1)) = 6 * (n + 1) ^ 2 := by ring
      have h3 : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow _ _ (Nat.succ_pos _)
      omega
  have hU_poly : ComputableInPolyTime
      (fun p : ((List Bool × List Bool) × ℕ) × List Bool =>
        universal (decodeDesc p.1.1.1, (frame p.1.1.2 ++ p.2).map eBit, capBudget e p))
      (encPair encB encBits) eOut :=
    hU.computableInPolyTime
      (hTp.add ((hIpoly.pow 4).mul (hBpoly.pow 2)))
      (hSp.add ((hIpoly.pow 2).mul hBpoly))
  have hv_poly : ComputableInPolyTime Diagonal.verdict eOut encBool :=
    Diagonal.computableInO_verdict_linear.computableInPolyTime
      (PolyBounded.of_forall_le 1 1 fun _ => by simp)
      (PolyBounded.of_forall_le 1 1 fun _ => by simp)
  have hnot_poly : ComputableInPolyTime (fun b : Bool => !b) encBool encBool :=
    (ComputableInDegree.of_finite (encIn := encBool) (encMid := encBool)
      fun b : Bool => !b).computableInPolyTime
  exact hnot_poly.comp (hv_poly.comp hU_poly)

attribute [local irreducible] ComputableInO Universal.decodeDesc Universal.eDesc in
/-- Exhaustive search at the end of an interval runs in time
`2 ^ (K * (|enc q| + certLen e |q.2|))`, using `capTest e` so the search predicate is
polynomial-time in the supplied unary certificate length `u` (and agrees with `budget e` when
`u = certLen e |q.2|`). -/
private theorem exists_computableInO_fineBrute (e : ℕ) :
    ∃ K, ComputableInO
      (fun q : List Bool × List Bool =>
        (Cslib.BitString.enumList (certLen e q.2.length)).any
          (Diagonal.lazyAccepts (budget e) q.1 q.2))
      (encPair encBits encBits) encBool
      (fun q => 2 ^ (K * ((encPair encBits encBits q).length + certLen e q.2.length)))
      (fun q => 2 ^ (K * ((encPair encBits encBits q).length + certLen e q.2.length))) := by
  set encQ := encPair encBits encBits with hencQ
  set encB := encPair encQ encUnary with hencB
  obtain ⟨Tf, Sf, hTf, hSf, hf⟩ := (computableInPolyTime_capTest e).exists_computableInO
  obtain ⟨K₀, hsearch⟩ := exists_computableInO_any_enumList hf hTf hSf
    (ComputableInPolyTime.snd encQ encUnary)
  have hExp0 : ComputableInPolyTime (fun y : List Bool => y.length - e * Nat.size (y.length + 1))
      encBits encUnary := by
    simpa only [Nat.add_zero] using computableInPolyTime_certExp e 0
  have hExp : ComputableInPolyTime (fun q : List Bool × List Bool =>
      q.2.length - e * Nat.size (q.2.length + 1)) encQ encUnary :=
    hExp0.comp (ComputableInPolyTime.snd encBits encBits)
  obtain ⟨C, hcl⟩ := hExp.exists_computableInO_unary_two_pow
  have hpair := (ComputableInO.of_eq (f := fun q : List Bool × List Bool => q) (encIn := encQ)
    (encMid := encQ) fun _ => rfl).prod hcl
  have h := hsearch.comp hpair
  refine ⟨3 * K₀ + 4, (h.mono (C + 3) (fun q => ?_) (fun q => ?_)).of_enc_eq fun q => ?_⟩
  rotate_left 2
  · simp only [Function.comp_apply, encBool_apply, List.cons.injEq, and_true]
    congr 1
    funext v
    change Diagonal.lazyAccepts (budget e) q.1 q.2 v = capTest e ((q, certLen e q.2.length), v)
    simp only [capTest, capBudget, Diagonal.lazyAccepts, budget, min_self]
  all_goals
    set N := (encQ q).length
    set c := certLen e q.2.length
    have hc1 : 1 ≤ c := Nat.one_le_two_pow
    have he1 : (encPair encQ encUnary (q, c)).length = 2 * N + 1 + c := by
      rw [length_encPair, encUnary_apply, List.length_replicate]
    have h4 : (4 : ℕ) ^ (q.2.length - e * Nat.size (q.2.length + 1)) = c * c := by
      rw [show c = 2 ^ (q.2.length - e * Nat.size (q.2.length + 1)) from rfl, ← mul_pow]
      norm_num
    have hbound := LazyDiagonal.brute_bound_aux C K₀ N c hc1
    have hcc1 : c ≤ c * c := Nat.le_mul_of_pos_left c hc1
    dsimp only [Function.comp_apply] at *
    rw [show 2 ^ (q.2.length - e * Nat.size (q.2.length + 1)) = c from rfl, he1]
    try rw [h4]
    omega

/-- **The fine exponential lazy diagonal is in `NTIME (2 ^ n)`** for all sufficiently large `e`
(depending only on the universal decoder degree) and all sufficiently large `c` (depending on
`e`). -/
theorem exists_fineExpLazyDiagonal_mem_NTIME :
    ∃ e₀, ∀ e, e₀ ≤ e → ∃ c₀, ∀ c, c₀ ≤ c →
      fineExpLazyDiagonal e c ∈ NTIME encBits fun n => 2 ^ n := by
  obtain ⟨dd, ed, hacc_all⟩ := exists_computableInO_fineAccepts
  refine ⟨6 * ed + 4, fun e he => ?_⟩
  obtain ⟨db, hacc⟩ := hacc_all e
  obtain ⟨K, hbrute⟩ := exists_computableInO_fineBrute e
  refine ⟨Nat.size (12 * K), fun c hc => ?_⟩
  -- 1. Certificate length in unary in time `O(2 ^ n)`
  have hExp := computableInPolyTime_certExp e 1
  obtain ⟨Te, Se, hTe, hSe, hExpO⟩ := hExp.exists_computableInO
  obtain ⟨CTe, hCTe⟩ := PolyBounded.exists_le_mul_two_pow hTe
  obtain ⟨CSe, hCSe⟩ := PolyBounded.exists_le_mul_two_pow hSe
  have hℓ : ComputableInO (fun x : List Bool => certLen e (x.length + 1)) encBits encUnary
      (fun x => (CTe + 2) * 2 ^ x.length) (fun x => (CSe + 2) * 2 ^ x.length) := by
    refine ((ComputableInO.unary_two_pow.comp hExpO).mono_le (fun x => ?_) (fun x => ?_)).of_enc_eq
      fun _ => rfl
    · have h1 := hCTe x
      have h2 := certExp_mul_certLen_le (by omega : 1 ≤ e) x.length
      simp only [encBits_apply] at h1 ⊢
      unfold certLen at h2
      rw [show x.length + 1 + 1 = x.length + 2 from rfl] at h2 ⊢
      have : (CTe + 2) * 2 ^ x.length = CTe * 2 ^ x.length + 2 * 2 ^ x.length := by ring
      omega
    · have h1 := hCSe x
      have h2 : 2 ^ (x.length + 1 - e * Nat.size (x.length + 2)) ≤ 2 * 2 ^ x.length := by
        have h3 : 2 ^ ((x.length + 1) - e * Nat.size (x.length + 2)) ≤ 2 ^ (x.length + 1) :=
          Nat.pow_le_pow_right Nat.one_lt_two.le (Nat.sub_le _ _)
        simpa only [pow_succ'] using h3
      simp only [encBits_apply] at h1 ⊢
      rw [show x.length + 1 + 1 = x.length + 2 from rfl]
      have : (CSe + 2) * 2 ^ x.length = CSe * 2 ^ x.length + 2 * 2 ^ x.length := by ring
      omega
  -- 2. The three tests run in `O(|enc p| + (|p.1| + 1) ^ dt)` (no unary horizon!)
  obtain ⟨d1, _, hd1⟩ := (computableInPolyTime_horizonTest c 1).exists_degree
  have hh2 : ComputableInPolyTime (fun x : List Bool =>
      decide (Nat.size x.length ≤ horizon c (2 * (unframe x).length + 1))) encBits encBool := by
    simpa only [Nat.add_zero] using computableInPolyTime_horizonTest c 0
  obtain ⟨d2, _, hd2⟩ := hh2.exists_degree
  set dt := max d1 d2
  let Ctest : List Bool × List Bool → ℕ := fun p =>
    (encPair encBits encBits p).length + (p.1.length + 1) ^ dt + 1
  have hfst := ComputableInO.fst encBits encBits
  have hc₀ : ComputableInO (fun p : List Bool × List Bool => Diagonal.shortDesc (unframe p.1))
      (encPair encBits encBits) encBool Ctest (fun p => 3 * Ctest p) := by
    have hunf : ComputableInO (fun p : List Bool × List Bool => unframe p.1)
        (encPair encBits encBits) encBits
        (fun p => (encPair encBits encBits p).length)
        (fun p => (encPair encBits encBits p).length) :=
      (ComputableInO.of_linear (.of_unframe fun _ => rfl)).comp hfst |>.mono 2
        (fun p => by
          have hn : p.1.length ≤ (encPair encBits encBits p).length := by
            simpa only [encBits_apply] using length_le_encPair_left encBits encBits p
          simp only [encBits_apply]
          omega)
        (fun p => by
          have hn : p.1.length ≤ (encPair encBits encBits p).length := by
            simpa only [encBits_apply] using length_le_encPair_left encBits encBits p
          simp only [encBits_apply]
          omega)
    have h0 := Diagonal.computableInO_shortDesc.comp hunf
    refine h0.mono 3 (fun p => ?_) (fun p => ?_)
    all_goals
      have hu := length_unframe_le p.1
      have hn : p.1.length ≤ (encPair encBits encBits p).length := by
        simpa only [encBits_apply] using length_le_encPair_left encBits encBits p
      dsimp only [Ctest, Function.comp_apply] at *
      omega
  have hmono_dt {f : List Bool → Bool} {d k : ℕ} (hd : d ≤ dt)
      (hf : ComputableInDegree f encBits encBool d k) :
      ComputableInO (fun p : List Bool × List Bool => f p.1) (encPair encBits encBits) encBool
        Ctest (fun p => (encPair encBits encBits p).length + (p.1.length + 1) ^ d) := by
    refine (hf.inO.comp hfst).mono_time 1 fun p => ?_
    have hpow : (p.1.length + 1) ^ d ≤ (p.1.length + 1) ^ dt :=
      Nat.pow_le_pow_right (Nat.succ_pos _) hd
    dsimp only [Ctest, Function.comp_apply, encBits_apply]
    omega
  have hc₁ := hmono_dt (le_max_left d1 d2) hd1
  have hc₂ := hmono_dt (le_max_right d1 d2) hd2
  -- 3. Assemble the lazy verifier
  obtain ⟨SV, hV⟩ := Diagonal.exists_computableInO_lazyVerifier hacc hbrute hc₀ hc₁ hc₂
    (fun p => by dsimp only [Ctest]; omega)
  -- 4. Absorb all polynomial-in-`n` terms into `O(2 ^ n)`
  obtain ⟨Cdd, hCdd⟩ := PolynomiallyBounded.exists_le_mul_two_pow
    (p := fun m => (m + 1) ^ dd) (by fun_prop)
  obtain ⟨Cdt, hCdt⟩ := PolynomiallyBounded.exists_le_mul_two_pow
    (p := fun n => (n + 1) ^ dt) (by fun_prop)
  obtain ⟨Cdb, hCdb⟩ := PolynomiallyBounded.exists_le_mul_two_pow
    (p := fun n => (n + 2) ^ db) (by fun_prop)
  obtain ⟨Csim, hCsim⟩ := PolynomiallyBounded.exists_le_mul_two_pow
    (p := fun n => (n + 2) ^ (6 * ed + 4)) (by fun_prop)
  set Ctotal := 6000 + CTe + 4 * Cdt + Cdd + Cdb + 2560 * Csim
  refine setOf_exists_mem_NTIME hℓ hV (C := Ctotal) fun x v hv => ?_
  set n := x.length with hn
  set V := certLen e (n + 1) with hVdef
  have hv' : v.length = V := hv
  have hVle : V ≤ 2 * 2 ^ n := by
    have h1 : 2 ^ ((n + 1) - e * Nat.size (n + 2)) ≤ 2 ^ (n + 1) :=
      Nat.pow_le_pow_right Nat.one_lt_two.le (Nat.sub_le _ _)
    simpa only [V, certLen, pow_succ'] using h1
  have hn2n : n + 1 ≤ 2 ^ n := Nat.lt_two_pow_self
  have h1_2n : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hCtest : Ctest (x, v) ≤ (6 + Cdt) * 2 ^ n := by
    have hdt := hCdt n
    have hlen : (encPair encBits encBits (x, v)).length ≤ 2 * n + 1 + 2 * 2 ^ n := by
      simp only [length_encPair, encBits_apply, hv', ← hn]; omega
    have heq : (6 + Cdt) * 2 ^ n = 6 * 2 ^ n + Cdt * 2 ^ n := by ring
    dsimp only [Ctest]
    rw [← hn]
    omega
  -- Simulation branch bound (when `shortDesc (unframe x) = true`)
  have hsim_bound (hs : Diagonal.shortDesc (unframe x) = true) :
      (Diagonal.encLazyAcceptsInput (unframe (unframe x), x ++ [false], v)).length +
        ((unframe (unframe x)).length + 1) ^ dd +
        ((x ++ [false]).length + 1) ^ db +
        (((unframe (unframe x)).length + 1) ^ ed + 1) ^ 6 *
          ((budget e (x ++ [false]) v + 1) * (Nat.log 2 (budget e (x ++ [false]) v + 1) + 1)) ≤
        (10 + Cdd + Cdb + 2560 * Csim + 5120) * 2 ^ n := by
    have hsh : 2 ^ (unframe (unframe x)).length ≤ (unframe x).length := of_decide_eq_true hs
    have hu := length_unframe_le x
    have hcode_le : (unframe (unframe x)).length ≤ n := by
      exact Nat.lt_two_pow_self.le.trans (hsh.trans (hu.trans (by omega)))
    have h1 : (Diagonal.encLazyAcceptsInput (unframe (unframe x), x ++ [false], v)).length ≤
        10 * 2 ^ n := by
      simp only [Diagonal.encLazyAcceptsInput, length_encPair, encBits_apply, List.length_append,
        List.length_singleton, hv', ← hn]
      omega
    have h2 : ((unframe (unframe x)).length + 1) ^ dd ≤ Cdd * 2 ^ n :=
      (hCdd _).trans (Nat.mul_le_mul_left _ (hsh.trans (hu.trans (by omega))))
    have h3 : ((x ++ [false]).length + 1) ^ db ≤ Cdb * 2 ^ n := by
      simpa only [List.length_append, List.length_singleton, ← hn] using hCdb n
    have hD6 : (((unframe (unframe x)).length + 1) ^ ed + 1) ^ 6 ≤ 64 * (n + 2) ^ (6 * ed) := by
      have hL : (unframe (unframe x)).length + 1 ≤ n + 2 := by omega
      have hDed : ((unframe (unframe x)).length + 1) ^ ed + 1 ≤ 2 * (n + 2) ^ ed := by
        have hpow := Nat.pow_le_pow_left hL ed
        have hpos : 1 ≤ (n + 2) ^ ed := Nat.one_le_pow _ _ (by omega)
        omega
      calc (((unframe (unframe x)).length + 1) ^ ed + 1) ^ 6
          ≤ (2 * (n + 2) ^ ed) ^ 6 := Nat.pow_le_pow_left hDed 6
        _ = 64 * (n + 2) ^ (6 * ed) := by rw [mul_pow, ← pow_mul, mul_comm ed 6]; norm_num
    have hbud_le : budget e (x ++ [false]) v + 1 ≤ 8 * (n + 2) ^ 2 * V := by
      have hV1 : 1 ≤ V := Nat.one_le_two_pow
      have hsz : Nat.size (n + 2) + 1 ≤ 2 * (n + 2) := by
        have : Nat.size (n + 2) ≤ n + 2 := Nat.size_le.2 Nat.lt_two_pow_self
        omega
      have hlin : 2 * (n + 1) + 2 + V ≤ 3 * (n + 2) * V := by
        have h3 : 2 * (n + 1) + 2 ≤ 2 * (n + 2) * V := by
          calc 2 * (n + 1) + 2 ≤ 2 * (n + 2) := by omega
            _ ≤ 2 * (n + 2) * V := Nat.le_mul_of_pos_right _ hV1
        have h4 : V ≤ (n + 2) * V := Nat.le_mul_of_pos_left V (by omega)
        have : 3 * (n + 2) * V = 2 * (n + 2) * V + (n + 2) * V := by ring
        omega
      simp only [budget, List.length_append, List.length_singleton, ← hn, ← hVdef]
      rw [show n + 1 + 1 = n + 2 from rfl]
      have hprod : (2 * (n + 1) + 2 + V) * (Nat.size (n + 2) + 1) ≤
          (3 * (n + 2) * V) * (2 * (n + 2)) := Nat.mul_le_mul hlin hsz
      have hpos : 1 ≤ (n + 2) ^ 2 * V := Nat.mul_pos (Nat.pow_pos (by omega)) hV1
      have : 8 * (n + 2) ^ 2 * V = (3 * (n + 2) * V) * (2 * (n + 2)) + 2 * ((n + 2) ^ 2 * V) := by
        ring
      omega
    have hlog_le : Nat.log 2 (budget e (x ++ [false]) v + 1) + 1 ≤ 5 * (n + 2) := by
      have hpow8 : 8 * (n + 2) ^ 2 * V ≤ 2 ^ (3 * n + 8) := by
        have h8n : 8 * (n + 2) ^ 2 ≤ 2 ^ (2 * n + 7) := by
          have hn2 : n + 2 ≤ 2 ^ (n + 2) := Nat.lt_two_pow_self.le
          have hsq : (n + 2) ^ 2 ≤ 2 ^ (2 * n + 4) := by
            calc (n + 2) ^ 2 ≤ (2 ^ (n + 2)) ^ 2 := Nat.pow_le_pow_left hn2 2
              _ = 2 ^ (2 * n + 4) := by rw [← pow_mul]; ring_nf
          calc 8 * (n + 2) ^ 2 ≤ 8 * 2 ^ (2 * n + 4) := Nat.mul_le_mul_left 8 hsq
            _ = 2 ^ (2 * n + 7) := by rw [show (8 : ℕ) = 2 ^ 3 by rfl, ← pow_add]; ring_nf
        calc 8 * (n + 2) ^ 2 * V ≤ 2 ^ (2 * n + 7) * (2 * 2 ^ n) := Nat.mul_le_mul h8n hVle
          _ = 2 ^ (3 * n + 8) := by
              rw [show 2 * 2 ^ n = 2 ^ (n + 1) from (pow_succ' 2 n).symm, ← pow_add]; ring_nf
      have hlg : Nat.log 2 (budget e (x ++ [false]) v + 1) ≤ 3 * n + 8 :=
        (Nat.log_mono_right (hbud_le.trans hpow8)).trans_eq (Nat.log_pow Nat.one_lt_two _)
      omega
    have hmain : (((unframe (unframe x)).length + 1) ^ ed + 1) ^ 6 *
        ((budget e (x ++ [false]) v + 1) * (Nat.log 2 (budget e (x ++ [false]) v + 1) + 1)) ≤
        (2560 * Csim + 5120) * 2 ^ n := by
      have hprod := Nat.mul_le_mul hD6 (Nat.mul_le_mul hbud_le hlog_le)
      have hrw : 64 * (n + 2) ^ (6 * ed) * (8 * (n + 2) ^ 2 * V * (5 * (n + 2))) =
          2560 * ((n + 2) ^ (6 * ed + 3) * V) := by
        rw [show 6 * ed + 3 = 6 * ed + 2 + 1 by omega, pow_succ, pow_add]
        ring
      have hmulV := pow_mul_certLen_le (e := e) (d := 6 * ed + 3) (by omega) n
      have hpow_le : (n + 2) ^ (6 * ed + 3) ≤ Csim * 2 ^ n :=
        (Nat.pow_le_pow_right (by omega) (by omega : 6 * ed + 3 ≤ 6 * ed + 4)).trans (hCsim n)
      calc _ ≤ 2560 * ((n + 2) ^ (6 * ed + 3) * V) := by rwa [← hrw]
        _ ≤ 2560 * ((n + 2) ^ (6 * ed + 3) + 2 * 2 ^ n) := Nat.mul_le_mul_left 2560 hmulV
        _ ≤ 2560 * (Csim * 2 ^ n + 2 * 2 ^ n) := Nat.mul_le_mul_left 2560 (by omega)
        _ = (2560 * Csim + 5120) * 2 ^ n := by ring
    have heq : (10 + Cdd + Cdb + 2560 * Csim + 5120) * 2 ^ n =
        10 * 2 ^ n + Cdd * 2 ^ n + Cdb * 2 ^ n + (2560 * Csim + 5120) * 2 ^ n := by ring
    omega
  -- Brute-force branch bound (when `¬ Nat.size (n + 1) ≤ horizon c P`)
  have hbrute_bound (h1 : ¬Nat.size (n + 1) ≤ horizon c (2 * (unframe x).length + 1)) :
      2 ^ (K * ((encPair encBits encBits (unframe (unframe x), frame (unframe x))).length +
        certLen e (2 * (unframe x).length + 1))) ≤ 2 ^ n := by
    set P := 2 * (unframe x).length + 1 with hP
    have hE : 2 ^ horizon c P ≤ n + 1 := by
      rw [Nat.size_le, not_lt] at h1
      exact h1
    have hcode_le := length_unframe_le (unframe x)
    have hP2 : P + 1 ≤ 2 ^ P := Nat.lt_two_pow_self
    have hcertP : certLen e P ≤ 2 ^ P :=
      Nat.pow_le_pow_right Nat.one_lt_two.le (Nat.sub_le _ _)
    have hlen : (encPair encBits encBits (unframe (unframe x), frame (unframe x))).length +
        certLen e P ≤ 4 * 2 ^ P := by
      have : (encPair encBits encBits (unframe (unframe x), frame (unframe x))).length ≤
          3 * P + 1 := by
        simp only [length_encPair, encBits_apply, length_frame]
        omega
      omega
    have hKpow : 4 * K ≤ 2 ^ c := by
      have hlt : 12 * K < 2 ^ Nat.size (12 * K) := Nat.lt_size_self _
      have hmono : 2 ^ Nat.size (12 * K) ≤ 2 ^ c := Nat.pow_le_pow_right Nat.one_lt_two.le hc
      omega
    have hexp : K * ((encPair encBits encBits (unframe (unframe x), frame (unframe x))).length +
        certLen e P) ≤ horizon c P := by
      calc K * ((encPair encBits encBits (unframe (unframe x), frame (unframe x))).length +
            certLen e P)
          ≤ K * (4 * 2 ^ P) := Nat.mul_le_mul_left K hlen
        _ = (4 * K) * 2 ^ P := by ring
        _ ≤ 2 ^ c * 2 ^ P := Nat.mul_le_mul_right _ hKpow
        _ = horizon c P := by rw [horizon, ← pow_add, add_comm]
    exact (Nat.pow_le_pow_right Nat.one_lt_two.le hexp).trans (hE.trans hn2n)
  -- Combine all branches
  simp only [encBits_apply]
  have hTeq : (CTe + 2) * 2 ^ n = CTe * 2 ^ n + 2 * 2 ^ n := by ring
  have hCtotal : Ctotal * 2 ^ n =
      6000 * 2 ^ n + CTe * 2 ^ n + 4 * (Cdt * 2 ^ n) + Cdd * 2 ^ n + Cdb * 2 ^ n +
        2560 * (Csim * 2 ^ n) := by dsimp only [Ctotal]; ring
  have hC4 : 4 * Ctest (x, v) ≤ 24 * 2 ^ n + 4 * (Cdt * 2 ^ n) := by
    have : 4 * ((6 + Cdt) * 2 ^ n) = 24 * 2 ^ n + 4 * (Cdt * 2 ^ n) := by ring
    have := Nat.mul_le_mul_left 4 hCtest
    omega
  rw [← hn]
  split_ifs with hs h1 h2
  · have hsim := hsim_bound hs
    have : (10 + Cdd + Cdb + 2560 * Csim + 5120) * 2 ^ n =
        5130 * 2 ^ n + Cdd * 2 ^ n + Cdb * 2 ^ n + 2560 * (Csim * 2 ^ n) := by ring
    omega
  · have hbr := hbrute_bound h1
    rw [length_frame]
    omega
  · omega
  · omega

/-! ### Fine exponential hierarchy theorems -/

/-- **Fine nondeterministic exponential time hierarchy** ([Zak1983]; [Williams2014], Section 3,
p. 8): there is an explicit constant `k` such that `NTIME (2 ^ n / (n + 1) ^ k)` is strictly
contained in `NTIME (2 ^ n)` on bit strings. -/
theorem exists_NTIME_two_pow_div_pow_ssubset :
    ∃ k : ℕ, NTIME encBits (fun n => 2 ^ n / (n + 1) ^ k) ⊂ NTIME encBits fun n => 2 ^ n := by
  obtain ⟨e₀, he₀⟩ := exists_fineExpLazyDiagonal_mem_NTIME
  obtain ⟨c₀, hc₀⟩ := he₀ e₀ le_rfl
  refine ⟨e₀ + 1, (Set.ssubset_iff_of_subset (NTIME_mono fun n => Nat.div_le_self _ _)).mpr
    ⟨fineExpLazyDiagonal e₀ c₀, hc₀ c₀ le_rfl, fineExpLazyDiagonal_notMem_NTIME e₀ c₀⟩⟩

/-- Subexponential savings lose more than every polynomial factor: for real `δ > 0`, `c₀ > 0` and
every `k`, eventually `⌊2 ^ (n - c₀ * n ^ δ)⌋₊ ≤ 2 ^ n / (n + 1) ^ k`. -/
theorem eventually_floor_two_pow_sub_rpow_le {δ c₀ : ℝ} (hδ : 0 < δ) (hc₀ : 0 < c₀) (k : ℕ) :
    ∀ᶠ n : ℕ in atTop, ⌊(2 : ℝ) ^ ((n : ℝ) - c₀ * (n : ℝ) ^ δ)⌋₊ ≤ 2 ^ n / (n + 1) ^ k := by
  have hlog := Nat.eventually_mul_log_add_pow_le_rpow (b := 2) Nat.one_lt_two 1 1 1
    (K := ((k : ℝ) + 1) / c₀) (by positivity) hδ
  filter_upwards [hlog] with n hn
  have h1 : ((k : ℝ) + 1) * ((Nat.log 2 (n + 1) : ℝ) + 1) ≤ c₀ * (n : ℝ) ^ δ := by
    rw [pow_one] at hn
    have := mul_le_mul_of_nonneg_left hn hc₀.le
    rw [← mul_assoc, mul_div_cancel₀ _ hc₀.ne'] at this
    push_cast at this
    exact this
  have h2 : ((n + 1 : ℕ) : ℝ) ^ k ≤ (2 : ℝ) ^ (c₀ * (n : ℝ) ^ δ) := by
    have hlt : (n + 1 : ℕ) ≤ 2 ^ (Nat.log 2 (n + 1) + 1) :=
      (Nat.lt_pow_succ_log_self Nat.one_lt_two (n + 1)).le
    have hltR : ((n + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (Nat.log 2 (n + 1) + 1 : ℕ) := by
      exact_mod_cast hlt
    have hpow : ((n + 1 : ℕ) : ℝ) ^ k ≤ (2 : ℝ) ^ ((k * (Nat.log 2 (n + 1) + 1) : ℕ) : ℝ) := by
      calc ((n + 1 : ℕ) : ℝ) ^ k
          ≤ ((2 : ℝ) ^ (Nat.log 2 (n + 1) + 1 : ℕ)) ^ k :=
            pow_le_pow_left₀ (by positivity) hltR k
        _ = (2 : ℝ) ^ (k * (Nat.log 2 (n + 1) + 1) : ℕ) := by
            rw [← pow_mul, mul_comm]
        _ = (2 : ℝ) ^ ((k * (Nat.log 2 (n + 1) + 1) : ℕ) : ℝ) := by rw [Real.rpow_natCast]
    have hexp : ((k * (Nat.log 2 (n + 1) + 1) : ℕ) : ℝ) ≤ c₀ * (n : ℝ) ^ δ := by
      have hk : (k : ℝ) ≤ (k : ℝ) + 1 := by linarith
      have hpos : (0 : ℝ) ≤ (Nat.log 2 (n + 1) : ℝ) + 1 := by positivity
      push_cast
      exact (mul_le_mul_of_nonneg_right hk hpos).trans h1
    exact hpow.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp)
  have hprodR : (⌊(2 : ℝ) ^ ((n : ℝ) - c₀ * (n : ℝ) ^ δ)⌋₊ : ℝ) * ((n + 1 : ℕ) : ℝ) ^ k ≤
      ((2 ^ n : ℕ) : ℝ) := by
    calc (⌊(2 : ℝ) ^ ((n : ℝ) - c₀ * (n : ℝ) ^ δ)⌋₊ : ℝ) * ((n + 1 : ℕ) : ℝ) ^ k
        ≤ (2 : ℝ) ^ ((n : ℝ) - c₀ * (n : ℝ) ^ δ) * ((n + 1 : ℕ) : ℝ) ^ k :=
          mul_le_mul_of_nonneg_right (Nat.floor_le (Real.rpow_nonneg (by norm_num) _))
            (by positivity)
      _ ≤ (2 : ℝ) ^ ((n : ℝ) - c₀ * (n : ℝ) ^ δ) * (2 : ℝ) ^ (c₀ * (n : ℝ) ^ δ) :=
          mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg (by norm_num) _)
      _ = (2 : ℝ) ^ (n : ℝ) := by
          rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2), sub_add_cancel]
      _ = ((2 ^ n : ℕ) : ℝ) := by rw [Real.rpow_natCast]; norm_cast
  have hprodN : ⌊(2 : ℝ) ^ ((n : ℝ) - c₀ * (n : ℝ) ^ δ)⌋₊ * (n + 1) ^ k ≤ 2 ^ n := by
    exact_mod_cast hprodR
  exact (Nat.le_div_iff_mul_le (Nat.pow_pos (Nat.succ_pos n))).2 hprodN

/-- **Subexponential-savings nondeterministic time hierarchy**: for every real `δ > 0` and
`c₀ > 0`, `NTIME (⌊2 ^ (n - c₀ * n ^ δ)⌋₊) ⊂ NTIME (2 ^ n)` on bit strings. -/
theorem NTIME_two_pow_sub_rpow_ssubset {δ c₀ : ℝ} (hδ : 0 < δ) (hc₀ : 0 < c₀) :
    NTIME encBits (fun n => ⌊(2 : ℝ) ^ ((n : ℝ) - c₀ * (n : ℝ) ^ δ)⌋₊) ⊂
      NTIME encBits fun n => 2 ^ n := by
  obtain ⟨k, hss⟩ := exists_NTIME_two_pow_div_pow_ssubset
  exact lt_of_le_of_lt
    (NTIME_mono_of_eventually_le (eventually_floor_two_pow_sub_rpow_le hδ hc₀ k)) hss

/-- **The subexponential-savings hierarchy at arbitrarily large lengths**: for every real `δ > 0`
and `c₀ > 0`, some problem in `NTIME (2 ^ n)` on bit strings differs from every problem in
`NTIME (⌊2 ^ (n - c₀ * n ^ δ)⌋₊)` at inputs of every sufficiently large length. In particular no
problem agreeing with it on all long inputs lies in the smaller class. -/
theorem exists_mem_NTIME_two_pow_forall_exists_length_ge {δ c₀ : ℝ} (hδ : 0 < δ) (hc₀ : 0 < c₀) :
    ∃ H ∈ NTIME encBits (fun n => 2 ^ n), ∀ B ∈ NTIME encBits
      (fun n => ⌊(2 : ℝ) ^ ((n : ℝ) - c₀ * (n : ℝ) ^ δ)⌋₊), ∀ N₀ : ℕ,
        ∃ y : List Bool, N₀ ≤ y.length ∧ ¬ (y ∈ H ↔ y ∈ B) := by
  obtain ⟨e₀, he₀⟩ := exists_fineExpLazyDiagonal_mem_NTIME
  obtain ⟨c, hc⟩ := he₀ e₀ le_rfl
  refine ⟨fineExpLazyDiagonal e₀ c, hc c le_rfl, fun B hB N₀ => ?_⟩
  exact exists_length_ge_fineExpLazyDiagonal_disagree e₀ c
    (NTIME_mono_of_eventually_le (eventually_floor_two_pow_sub_rpow_le hδ hc₀ (e₀ + 1)) hB) N₀

end Cslib.Complexity
