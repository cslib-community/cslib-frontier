/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.AKS.CongruenceLoop
public import CslibFrontier.Algorithms.WordRAM.AKS.GcdTotient
public import CslibFrontier.Algorithms.WordRAM.AKS.OrderSearch
public import CslibFrontier.Algorithms.WordRAM.AKS.PerfectPower
public import CslibFrontier.Algorithms.WordRAM.NatClog
public import CslibFrontier.Algorithms.WordRAM.NatSqrt
public import CslibFrontier.Computability.WordRAM.Compile
public import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Closure
public import CslibFrontier.Foundations.NumberTheory.AKS.IntegerVariant
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call
import CslibFrontier.Foundations.NumberTheory.AKS.SmallR

/-!
# The AKS primality test on the word RAM

The AKS algorithm [Agrawal, Kayal, Saxena, Section 4][AKS2004] decides whether `n` is prime. This
program runs it on the word RAM, with the input `n` in memory cell `1` and the integer thresholds
`c = ⌈log₂ n⌉` and `L = c²` (`Cslib.AKS.PassesUpTo`):

0. if `n < 2`, answer `0`;
1. if `n` is a perfect power, answer `0`;
2. find the least `r ≥ 2` with `ord_r(n) > L`;
3. if `1 < gcd(a, n) < n` for some `a ≤ r`, answer `0`;
4. if `n ≤ r`, answer `1`;
5. answer `1` exactly when `(X + a)^n ≡ X^n + a (mod X^r - 1, n)` for every
   `1 ≤ a ≤ ⌊√(φ(r) L)⌋`.

Each step is a subroutine run on the low registers. The search in step 2 stops by
`Cslib.AKS.exists_lt_orderOf`, at some `r ≤ 4 c⁵`, and the answer is correct by Theorem 4.1 of the
paper with integer thresholds (`Cslib.AKS.prime_iff_passesUpTo_numTestsNat`).

The word size must hold the numbers the steps compute; for an input of `s` bits, the width
`8 (s + 1)` suffices. The program then answers within `time s ≤ 4096 (s + 1)¹⁵` instructions
(`Cslib.Algorithms.WordRAM.AKS.time_le`). The dominant term is step 5: at most `2 s⁴` values of
`a`, each tested by `s` rounds of schoolbook multiplication of polynomials with `r ≤ 4 s⁵`
coefficients.
Theorem 5.1 of the paper bounds the bit complexity of the algorithm by `Õ(log^{21/2} n)`, using
fast multiplication of integers and polynomials.

## Main definitions

* `Cslib.Algorithms.WordRAM.AKS.program`: the AKS algorithm.
* `Cslib.Algorithms.WordRAM.AKS.time`: its instruction bound on inputs of `s` bits.

## Main results

* `Cslib.Algorithms.WordRAM.AKS.answers`: at a word size of at least `8 (size n + 1)`, the
  program answers whether `n` is prime within `time (size n)` instructions.
* `Cslib.Algorithms.WordRAM.AKS.decidesInTime`: its compiled program decides the primes.
* `Cslib.Algorithms.WordRAM.AKS.time_le`, `Cslib.Algorithms.WordRAM.AKS.polynomiallyBounded_time`:
  the instruction bound is at most `4096 (s + 1)¹⁵`, so it is polynomial.

## References

* [M. Agrawal, N. Kayal, N. Saxena, *PRIMES is in P*][AKS2004]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.AKS

open Cslib.WordRAM Cslib.AKS

/-! ### Registers -/

/-- Subroutines run on the low registers `0, …, k - 1`, below the registers of the top level. -/
def low {k : ℕ} (hk : k ≤ 29) : Fin k → Fin 36 := Fin.castLE (by omega)

theorem low_injective {k : ℕ} (hk : k ≤ 29) : (low hk).Injective := Fin.castLE_injective _

/-- The input `n`. -/
abbrev nv : Fin 36 := 29
/-- Constant one, which is also the address of the input. -/
abbrev one : Fin 36 := 30
/-- Constant two. -/
abbrev two : Fin 36 := 31
/-- The bound `L = ⌈log₂ n⌉²` on the order. -/
abbrev lv : Fin 36 := 32
/-- The modulus `r` of step 2. -/
abbrev rv : Fin 36 := 33
/-- Euler's totient `φ(r)`. -/
abbrev phv : Fin 36 := 34
/-- The answer. -/
abbrev ans : Fin 36 := 35

/-- The input of the perfect-power test. -/
abbrev ppN : Fin 36 := 0
/-- The answer of the perfect-power test. -/
abbrev ppFlag : Fin 36 := 11
/-- The argument of the binary logarithm. -/
abbrev logArg : Fin 36 := 0
/-- The binary logarithm. -/
abbrev logRes : Fin 36 := 1
/-- The number `n` of the search for `r`. -/
abbrev osN : Fin 36 := 0
/-- The bound `L` of the search for `r`. -/
abbrev osL : Fin 36 := 1
/-- The result `r` of the search. -/
abbrev osR : Fin 36 := 2
/-- The number `n` of step 3. -/
abbrev gtN : Fin 36 := 0
/-- The modulus `r` of step 3. -/
abbrev gtR : Fin 36 := 1
/-- The answer of step 3. -/
abbrev gtOk : Fin 36 := 4
/-- The totient computed in step 3. -/
abbrev gtPhi : Fin 36 := 5
/-- The argument of the square root. -/
abbrev sqArg : Fin 36 := 0
/-- The square root. -/
abbrev sqRoot : Fin 36 := 1
/-- The result block of step 5. -/
abbrev clR : Fin 36 := 0
/-- The base block of step 5. -/
abbrev clB : Fin 36 := 1
/-- The scratch block of step 5. -/
abbrev clT : Fin 36 := 2
/-- The number `r` of coefficients in step 5. -/
abbrev clRr : Fin 36 := 3
/-- The modulus `n` of step 5. -/
abbrev clNn : Fin 36 := 4
/-- The last tested value `A` of step 5. -/
abbrev clA : Fin 36 := 25
/-- The answer of step 5. -/
abbrev clOk : Fin 36 := 27

/-! ### The program -/

/-- Step 1, the perfect-power test. -/
def perfectPower : Code .standard 36 := PerfectPower.program.rename (low (by norm_num))

/-- The binary logarithm `⌈log₂ n⌉`. -/
def clog : Code .standard 36 := NatClog.program.rename (low (by norm_num))

/-- Step 2, the search for `r`. -/
def orderSearch : Code .standard 36 := OrderSearch.program.rename (low (by norm_num))

/-- Step 3, and the totient `φ(r)`. -/
def gcdTotient : Code .standard 36 := GcdTotient.program.rename (low (by norm_num))

/-- The integer square root. -/
def sqrt : Code .standard 36 := NatSqrt.program.rename (low (by norm_num))

/-- Step 5, the congruences. -/
def congruences : Code .standard 36 := CongruenceLoop.program.rename (low (by norm_num))

/-- Steps 4 and 5: answer `1` if `n ≤ r`, and otherwise test the congruence for
`1 ≤ a ≤ ⌊√(φ(r) L)⌋`, with the blocks at `0`, `r` and `2 r`. -/
def congruenceSteps : Code .standard 36 :=
  .branch (.lt rv nv)
    (.seq (ram[ sqArg ← phv * lv ]) (.seq sqrt
      (.seq (ram[ clA ← sqRoot; clR ← #0; clB ← rv; clT ← rv + rv; clRr ← rv; clNn ← nv ])
        (.seq congruences (ram[ ans ← clOk ])))))
    (ram[ ans ← #1 ])

/-- Steps 2 to 5, for an `n ≥ 2` that is not a perfect power. -/
def searchSteps : Code .standard 36 :=
  .seq (ram[ logArg ← nv ]) (.seq clog
    (.seq (ram[ lv ← logRes * logRes; osN ← nv; osL ← lv ]) (.seq orderSearch
    (.seq (ram[ rv ← osR; gtN ← nv; gtR ← rv ]) (.seq gcdTotient
    (.branch (.eq gtOk one) (.seq (ram[ phv ← gtPhi ]) congruenceSteps) (ram[ ans ← #0 ])))))))

/-- **The AKS algorithm.** Read `n`; answer `0` if `n < 2` or `n` is a perfect power, and
otherwise run steps 2 to 5. The answer is in `ans`. -/
def program : Code .standard 36 :=
  .seq (ram[ one ← #1; two ← #2; nv ← *one ])
    (.branch (.lt nv two) (ram[ ans ← #0 ])
      (.seq (ram[ ppN ← nv ]) (.seq perfectPower
        (.branch (.eq ppFlag one) (ram[ ans ← #0 ]) searchSteps))))

/-- The instruction bound of `program` on an input of `s` bits: the perfect-power test, the
logarithm, step 2 with `L ≤ s²` and `r ≤ 4 s⁵`, step 3, the square root, and step 5 with at most
`2 s⁴` tests. -/
def time (s : ℕ) : ℕ :=
  (s + 1) * (s * (6 * s + 13) + 6 * s + 22) + 9 * s + OrderSearch.time (s ^ 2) (4 * s ^ 5) +
    GcdTotient.time (4 * s ^ 5) + 10 * s ^ 4 +
    2 * s ^ 4 * (s * (2 * PolyPow.mulTime (4 * s ^ 5) + 6) + 104 * s ^ 5 + 67) + 70

/-- The instruction bound is a polynomial of degree `15`: `time s ≤ 4096 (s + 1)¹⁵`. -/
theorem time_le (s : ℕ) : time s ≤ 4096 * (s + 1) ^ 15 := by
  have h (k : ℕ) (hk : k ≤ 15) : s ^ k ≤ (s + 1) ^ 15 :=
    (Nat.pow_le_pow_left (Nat.le_succ s) k).trans (Nat.pow_le_pow_right (Nat.succ_pos s) hk)
  have h0 : 1 ≤ (s + 1) ^ 15 := Nat.one_le_pow _ _ (Nat.succ_pos s)
  have h1 : s ≤ (s + 1) ^ 15 := by simpa using h 1 (by norm_num)
  have h2 := h 2 (by norm_num); have h3 := h 3 (by norm_num); have h4 := h 4 (by norm_num)
  have h5 := h 5 (by norm_num); have h6 := h 6 (by norm_num); have h7 := h 7 (by norm_num)
  have h8 := h 8 (by norm_num); have h9 := h 9 (by norm_num); have h10 := h 10 (by norm_num)
  have h11 := h 11 (by norm_num); have h12 := h 12 (by norm_num)
  have h13 := h 13 (by norm_num); have h14 := h 14 (by norm_num); have h15 := h 15 le_rfl
  generalize (s + 1) ^ 15 = S at *
  unfold time OrderSearch.time GcdTotient.time PolyPow.mulTime
  ring_nf
  omega

/-- The instruction bound is polynomial in the number of bits. -/
theorem polynomiallyBounded_time : PolynomiallyBounded time :=
  PolynomiallyBounded.of_forall_le 4096 15 time_le

/-! ### Word sizes -/

/-- `s² ≤ 2^(s + 1)`. -/
private theorem sq_le_two_pow (s : ℕ) : s ^ 2 ≤ 2 ^ (s + 1) := by
  induction s with
  | zero => norm_num
  | succ k ih =>
    have hk : k < 2 ^ k := Nat.lt_two_pow_self
    have h1 : (k + 1) ^ 2 = k ^ 2 + 2 * k + 1 := by ring
    have h2 : 2 ^ (k + 1 + 1) = 2 ^ k * 4 := by ring
    have h3 : 2 ^ (k + 1) = 2 ^ k * 2 := by ring
    omega

/-- Numbers up to `64 s¹⁰` fit the width `8 (s + 1)`, for `s ≥ 2`. -/
private theorem fits_poly {w s v : ℕ} (hs : 2 ≤ s) (hw : 8 * (s + 1) ≤ w)
    (hv : v ≤ 64 * s ^ 10) : Fits w v := by
  have h10 : s ^ 10 ≤ 2 ^ (5 * s + 5) := by
    calc s ^ 10 = (s ^ 2) ^ 5 := by ring
      _ ≤ (2 ^ (s + 1)) ^ 5 := Nat.pow_le_pow_left (sq_le_two_pow s) 5
      _ = 2 ^ (5 * s + 5) := by ring
  refine fits_iff.mpr (lt_of_le_of_lt hv ?_)
  calc 64 * s ^ 10 ≤ 2 ^ 6 * 2 ^ (5 * s + 5) := by norm_num; omega
    _ = 2 ^ (5 * s + 11) := by ring
    _ < 2 ^ w := Nat.pow_lt_pow_right (by norm_num) (by omega)

/-- Numbers below `2^(2 s + 1)` fit the width `8 (s + 1)`. -/
private theorem fits_exp {w s v : ℕ} (hw : 8 * (s + 1) ≤ w) (hv : v < 2 ^ (2 * s + 1)) :
    Fits w v :=
  fits_iff.mpr (hv.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega)))

/-- For `N < 2^s` with `s ≥ 2`, `N² + 2 N + 2` fits the width `8 (s + 1)`. -/
private theorem fits_sq {w s N : ℕ} (hs : 2 ≤ s) (hw : 8 * (s + 1) ≤ w) (hN : N < 2 ^ s) :
    Fits w (N * N + 2 * N + 2) := by
  refine fits_exp hw ?_
  have : (N + 1) * (N + 1) ≤ 2 ^ s * 2 ^ s := Nat.mul_le_mul hN hN
  have h2 : 2 ^ (2 * s + 1) = 2 ^ s * 2 ^ s * 2 := by ring
  have h4 : 2 ≤ 2 ^ s := Nat.le_self_pow (by omega) 2
  rw [h2]
  nlinarith

/-- A register above the subroutine bank `[0, k)` is outside `low hk`. -/
private theorem low_ne {k : ℕ} (hk : k ≤ 29) {j : Fin 36} (hj : 29 ≤ j.val) (i : Fin k) :
    low hk i ≠ j := fun h => by
  have := congrArg Fin.val h
  dsimp [low] at this
  omega

/-! ### Correctness -/

/-- **Steps 4 and 5.** For `2 ≤ r ≤ 4 s⁵` and `L ≤ s²`, with `φ(r)` in `phv`, the answer is `1`
exactly when `n ≤ r` or the congruence holds for every `1 ≤ a ≤ ⌊√(φ(r) L)⌋`. -/
private theorem congruenceSteps_exec {w s : ℕ} (x : Data 36) {N R L : ℕ} (hn : x.regs nv = N)
    (hr : x.regs rv = R) (hl : x.regs lv = L) (hph : x.regs phv = Nat.totient R)
    (hsN : Nat.size N = s) (hs : 2 ≤ s) (hw : 8 * (s + 1) ≤ w) (hR : 2 ≤ R)
    (hRs : R ≤ 4 * s ^ 5) (hLs : L ≤ s ^ 2) :
    ∃ y, ExecWithin w congruenceSteps x y
      (2 * s ^ 4 * (s * (2 * PolyPow.mulTime (4 * s ^ 5) + 6) + 104 * s ^ 5 + 67) +
        10 * s ^ 4 + 22) ∧
      y.regs ans ≤ 1 ∧
      (y.regs ans = 1 ↔ N ≤ R ∨ ∀ a, 1 ≤ a → a ≤ Nat.sqrt (Nat.totient R * L) →
        Congruence N R a) := by
  have hNs : N < 2 ^ s := hsN ▸ Nat.lt_size_self N
  have h5 : s ^ 5 ≤ s ^ 10 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h7 : s ^ 7 ≤ s ^ 10 := Nat.pow_le_pow_right (by omega) (by norm_num)
  unfold congruenceSteps
  by_cases hRN : R < N
  swap
  · wram_exec [hr, hn, hRN, fits_poly hs hw (by omega : 1 ≤ 64 * s ^ 10)]
    wram_simp
    exact ⟨fun _ => Or.inl (by omega), fun _ => trivial⟩
  set Φ := Nat.totient R
  have hΦR : Φ ≤ R := Nat.totient_le R
  have hΦL : Φ * L ≤ 4 * s ^ 7 := by
    calc Φ * L ≤ (4 * s ^ 5) * s ^ 2 := Nat.mul_le_mul (hΦR.trans hRs) hLs
      _ = 4 * s ^ 7 := by ring
  set A := Nat.sqrt (Φ * L)
  have hA : A ≤ 2 * s ^ 4 := by
    calc A ≤ Nat.sqrt ((2 * s ^ 4) ^ 2) := Nat.sqrt_le_sqrt (by
          calc Φ * L ≤ 4 * s ^ 7 := hΦL
            _ ≤ 4 * s ^ 8 := Nat.mul_le_mul_left 4 (Nat.pow_le_pow_right (by omega) (by omega))
            _ = (2 * s ^ 4) ^ 2 := by ring)
      _ = 2 * s ^ 4 := Nat.sqrt_eq' _
  have h4 : s ^ 4 ≤ s ^ 10 := Nat.pow_le_pow_right (by omega) (by norm_num)
  unfold sqrt congruences
  wram_exec [hr, hn, hRN, hph, hl, fits_poly hs hw (by omega : Φ * L ≤ 64 * s ^ 10)]
  refine WP.name fun x₁ hx₁ => ?_
  have hx₁a : x₁.regs sqArg = Φ * L := by subst hx₁; wram_simp
  wram_call (NatSqrt.exec (x₁.comap (low (k := 6) (by norm_num)))
    (by change Fits w (4 * x₁.regs sqArg + 4); rw [hx₁a]; exact fits_poly hs hw (by omega)))
    renamed (low_injective _) with y₂ ⟨⟨hroot, -, -, -⟩, hout₂⟩
  have hroot' : y₂.regs sqRoot = A := by
    change y₂.regs sqRoot = Nat.sqrt (x₁.regs sqArg) at hroot
    rwa [hx₁a] at hroot
  have hy₂n : y₂.regs nv = N :=
    (hout₂ nv (low_ne _ (by decide))).trans (by subst hx₁; wram_simp [hn])
  have hy₂r : y₂.regs rv = R :=
    (hout₂ rv (low_ne _ (by decide))).trans (by subst hx₁; wram_simp [hr])
  wram_exec [hroot', hy₂r, hy₂n, fits_poly hs hw (by omega : R + R ≤ 64 * s ^ 10)]
  refine WP.name fun x₃ hx₃ => ?_
  wram_call (CongruenceLoop.exec (x₃.comap (low (k := 29) le_rfl))
    (a := 0) (b := R) (t := R + R) (r := R) (n := N) (A₀ := A)
    (by change x₃.regs clR = 0; subst hx₃; wram_simp)
    (by change x₃.regs clB = R; subst hx₃; wram_simp)
    (by change x₃.regs clT = R + R; subst hx₃; wram_simp)
    (by change x₃.regs clRr = R; subst hx₃; wram_simp)
    (by change x₃.regs clNn = N; subst hx₃; wram_simp)
    (by change x₃.regs clA = A; subst hx₃; wram_simp)
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (fits_poly hs hw (by omega)) (fits_poly hs hw (by omega)) (fits_poly hs hw (by omega))
    (fits_poly hs hw (by omega)) ((fits_sq hs hw hNs).of_le (by omega))
    (fits_poly hs hw (by omega)))
    renamed (low_injective _) with y₄ ⟨⟨hok, hokiff, -⟩, _⟩
  change y₄.regs clOk ≤ 1 at hok
  change y₄.regs clOk = 1 ↔ _ at hokiff
  wram_exec
  wram_simp [hok, hokiff]
  refine ⟨?_, Or.inr, fun h => h.resolve_left (by omega)⟩
  rw [show low (k := 6) (by norm_num) NatSqrt.arg = sqArg from rfl, hx₁a]
  have hmul : PolyPow.mulTime R ≤ PolyPow.mulTime (4 * s ^ 5) := by
    unfold PolyPow.mulTime; gcongr
  have hin : Nat.size N * (2 * PolyPow.mulTime R + 6) + 4 + 26 * R + 57 + 6 ≤
      s * (2 * PolyPow.mulTime (4 * s ^ 5) + 6) + 104 * s ^ 5 + 67 := by
    rw [hsN]
    have := Nat.mul_le_mul_left s
      (show 2 * PolyPow.mulTime R + 6 ≤ 2 * PolyPow.mulTime (4 * s ^ 5) + 6 by omega)
    omega
  have := Nat.mul_le_mul hA hin
  unfold CongruenceLoop.time Congruence.time PolyPow.time
  omega

/-- `n ≥ 2` has at least two bits. -/
private theorem two_le_size {N : ℕ} (hN : 2 ≤ N) : 2 ≤ Nat.size N := by
  by_contra h
  have := Nat.size_le.mp (by omega : Nat.size N ≤ 1)
  omega

/-- **Steps 2 to 5.** For `n ≥ 2` that is not a perfect power, at a word size of at least
`8 (size n + 1)`, the answer is `1` exactly when `n` is prime. -/
private theorem searchSteps_exec {w s : ℕ} (x : Data 36) {N : ℕ} (hn : x.regs nv = N)
    (h1 : x.regs one = 1) (hN : 2 ≤ N) (hpp : ¬ IsPerfectPower N) (hsN : Nat.size N = s)
    (hw : 8 * (s + 1) ≤ w) :
    ∃ y, ExecWithin w searchSteps x y
      (5 * s + OrderSearch.time (s ^ 2) (4 * s ^ 5) + GcdTotient.time (4 * s ^ 5) +
        (2 * s ^ 4 * (s * (2 * PolyPow.mulTime (4 * s ^ 5) + 6) + 104 * s ^ 5 + 67) +
          10 * s ^ 4 + 22) + 20) ∧
      y.regs ans ≤ 1 ∧ (y.regs ans = 1 ↔ N.Prime) := by
  have hs : 2 ≤ s := hsN ▸ two_le_size hN
  have hNs : N < 2 ^ s := hsN ▸ Nat.lt_size_self N
  obtain ⟨c, hcdef⟩ : ∃ c, Nat.clog 2 N = c := ⟨_, rfl⟩
  have hc : c ≤ s := hcdef ▸ Nat.clog_le_of_le_pow hNs.le
  have hcc : c * c ≤ s ^ 2 := by rw [sq]; exact Nat.mul_le_mul hc hc
  have h1s : s ≤ s ^ 2 := by nlinarith
  have h2s : s ^ 2 ≤ s ^ 10 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h5s : s ^ 5 ≤ s ^ 10 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hF2 : Fits w 2 := fits_poly hs hw (by omega)
  have hFN : Fits w N := fits_exp hw (hNs.trans (Nat.pow_lt_pow_right (by norm_num) (by omega)))
  have hFN1 : Fits w (N + 1) :=
    fits_exp hw (lt_of_le_of_lt hNs (Nat.pow_lt_pow_right (by norm_num) (by omega)))
  unfold searchSteps clog orderSearch gcdTotient
  wram_exec [hn]
  refine WP.name fun x₁ hx₁ => ?_
  have hx₁a : x₁.regs logArg = N := by subst hx₁; wram_simp
  wram_call (NatClog.exec (x₁.comap (low (k := 4) (by norm_num))) hF2
    (by change Fits w (x₁.regs logArg + 1); exact hx₁a ▸ hFN1)
    (by change Fits w (Nat.clog 2 (x₁.regs logArg) + 1); rw [hx₁a, hcdef]
        exact fits_poly hs hw (by omega)))
    renamed (low_injective _) with y₂ ⟨⟨hres, -, -, -⟩, hout₂⟩
  have hres' : y₂.regs logRes = c := by
    change y₂.regs logRes = Nat.clog 2 (x₁.regs logArg) at hres
    rwa [hx₁a, hcdef] at hres
  have hy₂n : y₂.regs nv = N :=
    (hout₂ nv (low_ne _ (by decide))).trans (by subst hx₁; wram_simp [hn])
  have hy₂1 : y₂.regs one = 1 :=
    (hout₂ one (low_ne _ (by decide))).trans (by subst hx₁; wram_simp [h1])
  wram_exec [hres', hy₂n, fits_poly hs hw (by omega : c * c ≤ 64 * s ^ 10)]
  refine WP.name fun x₃ hx₃ => ?_
  obtain ⟨r₀, hr₀2, hr₀s, hr₀ord⟩ := exists_lt_orderOf hN
  rw [hcdef] at hr₀s hr₀ord
  have hr₀s' : r₀ ≤ 4 * s ^ 5 := hr₀s.trans (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left hc 5))
  have hgood : OrderSearch.Good N (c * c) r₀ := (lt_orderOf_iff hr₀2).mp (by rwa [← sq])
  have hFr₀ : Fits w (r₀ * r₀) := fits_poly hs hw (by
    calc r₀ * r₀ ≤ (4 * s ^ 5) * (4 * s ^ 5) := Nat.mul_le_mul hr₀s' hr₀s'
      _ = 16 * s ^ 10 := by ring
      _ ≤ 64 * s ^ 10 := by omega)
  wram_call (OrderSearch.exec (x₃.comap (low (k := 13) (by norm_num))) (N := N) (L₀ := c * c)
    (r₀ := r₀) (by change x₃.regs osN = N; subst hx₃; wram_simp)
    (by change x₃.regs osL = c * c; subst hx₃; wram_simp)
    hr₀2 hgood hFN hFr₀ (fits_poly hs hw (by omega)))
    renamed (low_injective _) with y₄ ⟨⟨hR2, hRr₀, hRgood, -, -⟩, hout₄⟩
  obtain ⟨R, hRdef⟩ : ∃ R, y₄.regs osR = R := ⟨_, rfl⟩
  change 2 ≤ y₄.regs osR at hR2
  change y₄.regs osR ≤ r₀ at hRr₀
  change OrderSearch.Good N (c * c) (y₄.regs osR) at hRgood
  rw [hRdef] at hR2 hRr₀ hRgood
  have hRs : R ≤ 4 * s ^ 5 := hRr₀.trans hr₀s'
  have hy₄n : y₄.regs nv = N :=
    (hout₄ nv (low_ne _ (by decide))).trans (by subst hx₃; wram_simp [hy₂n])
  have hy₄l : y₄.regs lv = c * c :=
    (hout₄ lv (low_ne _ (by decide))).trans (by subst hx₃; wram_simp)
  have hy₄1 : y₄.regs one = 1 :=
    (hout₄ one (low_ne _ (by decide))).trans (by subst hx₃; wram_simp [hy₂1])
  wram_exec [hRdef, hy₄n]
  refine WP.name fun x₅ hx₅ => ?_
  wram_call (GcdTotient.exec (x₅.comap (low (k := 11) (by norm_num))) (N := N) (R := R)
    (by change x₅.regs gtN = N; subst hx₅; wram_simp)
    (by change x₅.regs gtR = R; subst hx₅; wram_simp)
    hR2 hFN (fits_poly hs hw (by omega)))
    renamed (low_injective _) with y₆ ⟨⟨hok, hokiff, hphi, -, -⟩, hout₆⟩
  change y₆.regs gtOk = 1 ↔ _ at hokiff
  change y₆.regs gtPhi = Nat.totient R at hphi
  have hy₆n : y₆.regs nv = N :=
    (hout₆ nv (low_ne _ (by decide))).trans (by subst hx₅; wram_simp [hy₄n])
  have hy₆r : y₆.regs rv = R :=
    (hout₆ rv (low_ne _ (by decide))).trans (by subst hx₅; wram_simp)
  have hy₆l : y₆.regs lv = c * c :=
    (hout₆ lv (low_ne _ (by decide))).trans (by subst hx₅; wram_simp [hy₄l])
  have hy₆1 : y₆.regs one = 1 :=
    (hout₆ one (low_ne _ (by decide))).trans (by subst hx₅; wram_simp [hy₄1])
  have hord : Nat.clog 2 N ^ 2 < orderOf (N : ZMod R) := by
    rw [hcdef, sq]; exact (lt_orderOf_iff hR2).mpr hRgood
  have hprime := prime_iff_passesUpTo_numTestsNat hN hord
  have hOS : OrderSearch.time (c * c) r₀ ≤ OrderSearch.time (s ^ 2) (4 * s ^ 5) := by
    unfold OrderSearch.time; gcongr
  have hGT : GcdTotient.time R ≤ GcdTotient.time (4 * s ^ 5) := by
    unfold GcdTotient.time; gcongr
  by_cases h3 : y₆.regs gtOk = 1
  · wram_exec [h3, hy₆1, hphi]
    refine WP.name fun x₇ hx₇ => ?_
    wram_call (congruenceSteps_exec (w := w) x₇ (N := N) (R := R) (L := c * c)
      (by subst hx₇; wram_simp [hy₆n]) (by subst hx₇; wram_simp [hy₆r])
      (by subst hx₇; wram_simp [hy₆l]) (by subst hx₇; wram_simp) hsN hs hw hR2 hRs hcc)
      with z ⟨hz1, hziff⟩
    refine ⟨?_, hz1, ?_⟩
    · rw [show low (k := 4) (by norm_num) NatClog.arg = logArg from rfl, hx₁a, hcdef]; omega
    · rw [hziff, hprime, PassesUpTo, numTestsNat, hcdef, sq]
      exact ⟨fun h => ⟨hpp, hokiff.mp h3, h⟩, fun h => h.2.2⟩
  · wram_exec [h3, hy₆1]
    wram_simp
    refine ⟨?_, nofun, fun hp => h3 (hokiff.mpr (passesUpTo_of_prime hp R 0).2.1)⟩
    rw [show low (k := 4) (by norm_num) NatClog.arg = logArg from rfl, hx₁a, hcdef]; omega

/-- **The AKS algorithm is correct.** At a word size of at least `8 (size n + 1)`, the program
leaves `1` in `ans` if `n` is prime and `0` otherwise, within `time (size n)` instructions. -/
theorem answers {w : ℕ} (N : ℕ) (hw : 8 * (Nat.size N + 1) ≤ w) :
    program.Answers ans w [N] N.Prime (time (Nat.size N)) := by
  obtain ⟨s, hsN⟩ : ∃ s, Nat.size N = s := ⟨_, rfl⟩
  rw [hsN] at hw ⊢
  have hNs : N < 2 ^ s := hsN ▸ Nat.lt_size_self N
  have h8 : 2 ^ 8 ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hF1 : Fits w 1 := fits_iff.mpr (by omega)
  have hF2 : Fits w 2 := fits_iff.mpr (by omega)
  have hmem : (Data.init [N] : Data 36).mem 1 = N := rfl
  unfold Code.Answers program perfectPower
  by_cases hN : N < 2
  · wram_exec [hmem, hF1, hF2, hN]
    wram_simp
    exact ⟨by unfold time; omega, nofun, fun hp => absurd hp.two_le (by omega)⟩
  have hN2 : 2 ≤ N := by omega
  have hs : 2 ≤ s := hsN ▸ two_le_size hN2
  wram_exec [hmem, hF1, hF2, hN]
  refine WP.name fun x₂ hx₂ => ?_
  have hx₂n : x₂.regs ppN = N := by subst hx₂; wram_simp
  wram_call (PerfectPower.exec (x₂.comap (low (k := 14) (by norm_num)))
    (by change 2 ≤ x₂.regs ppN; exact hx₂n ▸ hN2)
    (by change Fits w (x₂.regs ppN * x₂.regs ppN + 2 * x₂.regs ppN + 2)
        exact hx₂n ▸ fits_sq hs hw hNs))
    renamed (low_injective _) with y₃ ⟨⟨hflag, -, -⟩, hout₃⟩
  have hpp_eq : IsPerfectPower (x₂.regs (low (k := 14) (by norm_num) PerfectPower.n)) ↔
      IsPerfectPower N := by
    rw [show low (k := 14) (by norm_num) PerfectPower.n = ppN from rfl, hx₂n]
  have hy₃n : y₃.regs nv = N :=
    (hout₃ nv (low_ne _ (by decide))).trans (by subst hx₂; wram_simp)
  have hy₃1 : y₃.regs one = 1 :=
    (hout₃ one (low_ne _ (by decide))).trans (by subst hx₂; wram_simp)
  have hPP : PerfectPower.time N ≤ (s + 1) * (s * (6 * s + 13) + 6 * s + 22) + 4 * s + 11 := by
    have hlog : Nat.log 2 N ≤ s := (Nat.log_lt_of_lt_pow (by omega) hNs).le
    have hclog : Nat.clog 2 (N + 1) ≤ s := Nat.clog_le_of_le_pow hNs
    unfold PerfectPower.time; gcongr
  by_cases hpp : IsPerfectPower N
  · have hflag1 : y₃.regs ppFlag = 1 := hflag.trans (ite_eq_left (hpp_eq.mpr hpp))
    wram_exec [hflag1, hy₃1]
    wram_simp
    refine ⟨?_, nofun, fun hp => not_isPerfectPower_of_prime hp hpp⟩
    rw [show low (k := 14) (by norm_num) PerfectPower.n = ppN from rfl, hx₂n]
    unfold time; omega
  · have hflag0 : y₃.regs ppFlag = 0 := hflag.trans (ite_eq_right (mt hpp_eq.mp hpp))
    wram_exec [hflag0, hy₃1]
    wram_call (searchSteps_exec y₃ hy₃n hy₃1 hN2 hpp hsN hw) with z ⟨hz1, hziff⟩
    refine ⟨?_, hz1, hziff⟩
    rw [show low (k := 14) (by norm_num) PerfectPower.n = ppN from rfl, hx₂n]
    unfold time; omega

/-- **The AKS algorithm decides the primes.** Its compiled program, given `n` as one word at a word
size of at least `8 (size n + 1)`, answers whether `n` is prime within `time (size n) + 1`
instructions. -/
theorem decidesInTime :
    (program.program ans).DecidesInTime (fun _ n => [n]) {n : ℕ | n.Prime}
      (fun n _ => time (Nat.size n) + 1) (fun n w => 8 * (Nat.size n + 1) ≤ w) :=
  program.decidesInTime_program (time := fun n _ => time (Nat.size n)) ans
    fun n _ hw _ => answers n hw

end Cslib.Algorithms.WordRAM.AKS
