/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.TSP.HamiltonianCount
public import CslibFrontier.Computability.WordRAM.Function
import CslibFrontier.Computability.WordRAM.CountingLoop
import CslibFrontier.Computability.WordRAM.Notation
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call
import CslibFrontier.Foundations.Data.List.RowMajor
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Karp–Bax inclusion–exclusion Hamiltonian path counting on the word RAM

Checked standard-basis word-RAM (`Cslib.WordRAM.Basis.standard`) implementation of Karp and Bax's
inclusion–exclusion Hamiltonian-path counter (`CslibFrontier.Algorithms.Lean.TSP.HamiltonianCount`)
[Karp1982] [Bax1993] ([FominKratsch2010], Section 4.2.2, Theorem 4.5 and Eq. (4.4)):

* **`program`**: given an `n`-vertex directed graph `I : Instance` encoded as `I.n` followed by
  the `n × n` row-major adjacency matrix (`0`/`1` words), computes `#(hamPaths I.adj)` in at most
  `64 * ((I.n ^ 3 + 1) * 2 ^ I.n)` instructions at every width `w` with `I.FitsWidth w`.
* **`decideProgram`**: decides `(hamPaths I.adj).Nonempty` (returning `1` or `0`) within the same
  `64 * ((I.n ^ 3 + 1) * 2 ^ I.n)` instruction bound.

Subsets `S ⊆ Fin n` are enumerated in place using an `n`-word binary odometer `inMask[0..n-1]`
and parity bit `maskParity = #S % 2`, keeping working memory to `3 * n` words right after the
input matrix (`inMask`, `cur`, `next`) plus scalar registers. Neither program uses bitwise
instructions, `width%`, or `rand`.

## Word-size condition

During every mask `k < 2 ^ n` and round `r < n`, every entry `walkCountFrom I.adj S r u` is at
most `n ^ r`, so `totalWalkCount I.adj S ≤ (n + 1) ^ n` and both partial sums `evenSum` and
`oddSum` stay at most `2 ^ n * (n + 1) ^ n`. The envelope
`I.wordBound = 4 * (2 ^ I.n * (I.n + 1) ^ I.n + (I.n + 1) ^ 2 + 16)` (requiring `O(n log n)`-bit
words, matching [FominKratsch2010], Section 4.2.2) covers the input, all working addresses, and all
accumulated walk counts.

## References

* [E. T. Bax, *Inclusion and exclusion algorithm for the Hamiltonian path problem*][Bax1993]
* [F. V. Fomin and D. Kratsch, *Exact Exponential Algorithms*][FominKratsch2010], Section 4.2.2
* [R. M. Karp, *Dynamic programming meets the principle of inclusion and exclusion*][Karp1982]
-/

public section

namespace Cslib.Algorithms.WordRAM.HamiltonianCount

open Cslib.Algorithms.Lean.TSP
open Cslib.Algorithms.Lean.Yates
open Cslib.WordRAM
open Finset

/-! ## Encoded instances and walk-count bounds -/

/-- A directed graph on `Fin n` given by its boolean adjacency matrix. -/
structure Instance where
  /-- Number of vertices `n`. -/
  n : ℕ
  /-- Adjacency predicate `adj u v = true` when `(u, v)` is an arc. -/
  adj : Fin n → Fin n → Bool

namespace Instance

/-- Flat Word-RAM input `[n] ++ rowMajor adj`. -/
@[expose] def encode (I : Instance) : List ℕ :=
  I.n :: (List.finRange I.n).flatMap fun u =>
    List.ofFn fun v => if I.adj u v then 1 else 0

/-- Word-size envelope covering the input matrix, `O(n²)` working addresses, and `n^n`-scale walk
counts accumulated across `2 ^ n` subsets. -/
@[expose] def wordBound (I : Instance) : ℕ :=
  4 * (2 ^ I.n * (I.n + 1) ^ I.n + (I.n + 1) ^ 2 + 16)

/-- Width admissibility predicate for `Instance`. -/
@[expose] def FitsWidth (I : Instance) (w : ℕ) : Prop :=
  Fits w I.wordBound

private theorem one_le_word_prod (n : ℕ) : 1 ≤ 2 ^ n * (n + 1) ^ n :=
  Nat.mul_pos Nat.one_le_two_pow (Nat.one_le_pow _ _ (by omega))

@[simp] theorem length_encode (I : Instance) : I.encode.length = I.n * I.n + 1 := by
  simp [encode, List.length_flatMap]

theorem inputFits (I : Instance) {w : ℕ} (hfit : I.FitsWidth w) : InputFits w I.encode := by
  have h1 : 1 ≤ 2 ^ I.n * (I.n + 1) ^ I.n := one_le_word_prod I.n
  refine ⟨hfit.of_le (by simp only [length_encode]; unfold wordBound; nlinarith), ?_⟩
  intro x hx
  simp only [encode, List.mem_cons, List.mem_flatMap, List.mem_finRange, true_and,
    List.mem_ofFn] at hx
  rcases hx with rfl | ⟨u, v, rfl⟩
  · exact hfit.of_le (by unfold wordBound; nlinarith)
  · split_ifs <;> exact hfit.of_le (by unfold wordBound; nlinarith)

theorem init_mem_n (I : Instance) {r : ℕ} : (Data.init I.encode : Data r).mem 1 = I.n := by
  change (Data.init I.encode : Data r).mem (0 + 1) = I.n
  rw [Data.init_mem_succ]
  rfl

theorem init_mem_adj (I : Instance) {r : ℕ} (u v : Fin I.n) :
    (Data.init I.encode : Data r).mem (2 + u.1 * I.n + v.1) = if I.adj u v then 1 else 0 := by
  rw [show (2 : ℕ) + u.1 * I.n + v.1 = ((u.1 * I.n + v.1) + 1) + 1 by omega,
    Data.init_mem_succ]
  simp only [encode, List.getD_cons_succ]
  exact List.getD_flatMap_ofFn (fun u v => if I.adj u v then 1 else 0) 0 u v

end Instance

private theorem one_le_word_prod (n : ℕ) : 1 ≤ 2 ^ n * (n + 1) ^ n :=
  Instance.one_le_word_prod n

private theorem adj_index_lt {n : ℕ} (u v : Fin n) : u.1 * n + v.1 < n * n := by
  have := Nat.mul_le_mul_right n (Nat.lt_iff_add_one_le.mp u.isLt)
  calc u.1 * n + v.1 < u.1 * n + n := Nat.add_lt_add_left v.isLt _
    _ = (u.1 + 1) * n := by ring
    _ ≤ n * n := this

private theorem walkCountFrom_le_pow {n : ℕ} (adj : Fin n → Fin n → Bool) (S : Finset (Fin n))
    (r : ℕ) (u : Fin n) : walkCountFrom adj S r u ≤ n ^ r := by
  induction r generalizing u with
  | zero =>
    simp only [walkCountFrom, pow_zero]
    split_ifs <;> omega
  | succ r ih =>
    rw [walkCountFrom, pow_succ']
    calc
      ∑ v : Fin n, (if u ∈ S ∧ adj u v then walkCountFrom adj S r v else 0)
          ≤ ∑ _v : Fin n, n ^ r := by
            refine Finset.sum_le_sum fun v _ => ?_
            split_ifs
            · exact ih v
            · exact Nat.zero_le _
      _ = n * n ^ r := by simp

private theorem totalWalkCount_le {n : ℕ} (adj : Fin n → Fin n → Bool) (S : Finset (Fin n)) :
    totalWalkCount adj S ≤ (n + 1) ^ n := by
  cases n with
  | zero => simp [totalWalkCount]
  | succ m =>
    rw [totalWalkCount]
    calc
      ∑ u : Fin (m + 1), walkCountFrom adj S m u
          ≤ ∑ _u : Fin (m + 1), (m + 1) ^ m :=
            Finset.sum_le_sum fun u _ => walkCountFrom_le_pow adj S m u
      _ = (m + 1) * (m + 1) ^ m := by simp
      _ = (m + 1) ^ (m + 1) := by rw [← pow_succ']
      _ ≤ (m + 2) ^ (m + 1) := Nat.pow_le_pow_left (by omega) _

/-! ## Word-RAM program -/

private abbrev nReg : Fin 22 := ⟨0, by decide⟩
private abbrev oneReg : Fin 22 := ⟨1, by decide⟩
private abbrev twoReg : Fin 22 := ⟨2, by decide⟩
private abbrev adjBase : Fin 22 := ⟨3, by decide⟩
private abbrev inBase : Fin 22 := ⟨4, by decide⟩
private abbrev curBase : Fin 22 := ⟨5, by decide⟩
private abbrev nextBase : Fin 22 := ⟨6, by decide⟩
private abbrev maskLimit : Fin 22 := ⟨7, by decide⟩
private abbrev kReg : Fin 22 := ⟨8, by decide⟩
private abbrev nParity : Fin 22 := ⟨9, by decide⟩
private abbrev maskParity : Fin 22 := ⟨10, by decide⟩
private abbrev evenSum : Fin 22 := ⟨11, by decide⟩
private abbrev oddSum : Fin 22 := ⟨12, by decide⟩
private abbrev iReg : Fin 22 := ⟨13, by decide⟩
private abbrev rReg : Fin 22 := ⟨14, by decide⟩
private abbrev nMinus1 : Fin 22 := ⟨15, by decide⟩
private abbrev uReg : Fin 22 := ⟨16, by decide⟩
private abbrev vReg : Fin 22 := ⟨17, by decide⟩
private abbrev accReg : Fin 22 := ⟨18, by decide⟩
private abbrev addr1 : Fin 22 := ⟨19, by decide⟩
private abbrev addr2 : Fin 22 := ⟨20, by decide⟩
private abbrev tmpReg : Fin 22 := ⟨21, by decide⟩

private def copyVec (srcReg dstReg : Fin 22) : Code .standard 22 := ram[
  iReg ← #0;
  while iReg < nReg do [
    addr1 ← srcReg + iReg;
    tmpReg ← *addr1;
    addr2 ← dstReg + iReg;
    *addr2 ← tmpReg;
    iReg ← iReg + oneReg
  ]
]

private def stepCellCode : Code .standard 22 := ram[
  addr1 ← inBase + uReg;
  tmpReg ← *addr1;
  if tmpReg = oneReg then [
    accReg ← #0;
    vReg ← #0;
    addr2 ← uReg * nReg;
    addr2 ← adjBase + addr2;
    while vReg < nReg do [
      addr1 ← addr2 + vReg;
      tmpReg ← *addr1;
      if tmpReg = oneReg then [
        addr1 ← curBase + vReg;
        tmpReg ← *addr1;
        accReg ← accReg + tmpReg
      ] else [
        tmpReg ← #0
      ];
      vReg ← vReg + oneReg
    ]
  ] else [
    accReg ← #0
  ];
  addr1 ← nextBase + uReg;
  *addr1 ← accReg;
  uReg ← uReg + oneReg
]

private def stepVecCode : Code .standard 22 := ram[
  uReg ← #0;
  while uReg < nReg do [
    ⟪stepCellCode⟫
  ]
]

private def roundsCode : Code .standard 22 := ram[
  rReg ← #0;
  while rReg < nMinus1 do [
    ⟪stepVecCode⟫;
    ⟪copyVec nextBase curBase⟫;
    rReg ← rReg + oneReg
  ]
]

private def sumVecCode : Code .standard 22 := ram[
  accReg ← #0;
  iReg ← #0;
  while iReg < nReg do [
    addr1 ← curBase + iReg;
    tmpReg ← *addr1;
    accReg ← accReg + tmpReg;
    iReg ← iReg + oneReg
  ]
]

private def odometerCode : Code .standard 22 := ram[
  iReg ← #0;
  while iReg < nReg do [
    addr1 ← inBase + iReg;
    accReg ← *addr1;
    if accReg = oneReg then [
      tmpReg ← #0;
      *addr1 ← tmpReg;
      maskParity ← oneReg - maskParity;
      iReg ← iReg + oneReg
    ] else [
      *addr1 ← oneReg;
      maskParity ← oneReg - maskParity;
      iReg ← nReg
    ]
  ]
]

private def maskBodyCode : Code .standard 22 := ram[
  tmpReg ← #0;
  if tmpReg < nReg then [
    ⟪copyVec inBase curBase⟫;
    ⟪roundsCode⟫;
    ⟪sumVecCode⟫
  ] else [
    accReg ← #1
  ];
  if maskParity = nParity then [
    evenSum ← evenSum + accReg
  ] else [
    oddSum ← oddSum + accReg
  ];
  ⟪odometerCode⟫;
  kReg ← kReg + oneReg
]

private def initRegsCode : Code .standard 22 := ram[
  oneReg ← #1;
  twoReg ← #2;
  adjBase ← #2;
  nReg ← *oneReg;
  nMinus1 ← nReg - oneReg;
  nParity ← nReg % twoReg;
  evenSum ← #0;
  oddSum ← #0;
  maskParity ← #0;
  inBase ← nReg * nReg;
  inBase ← inBase + twoReg;
  curBase ← inBase + nReg;
  nextBase ← curBase + nReg;
  maskLimit ← #1;
  iReg ← #0
]

private def countHamInitCode : Code .standard 22 := ram[
  ⟪initRegsCode⟫;
  while iReg < nReg do [
    maskLimit ← maskLimit + maskLimit;
    iReg ← iReg + oneReg
  ];
  iReg ← #0;
  while iReg < nReg do [
    addr1 ← inBase + iReg;
    *addr1 ← oddSum;
    iReg ← iReg + oneReg
  ]
]

private def countHamCode : Code .standard 22 := ram[
  ⟪countHamInitCode⟫;
  kReg ← #0;
  while kReg < maskLimit do [
    ⟪maskBodyCode⟫
  ];
  evenSum ← evenSum - oddSum
]

private def decideHamCode : Code .standard 22 := ram[
  ⟪countHamCode⟫;
  tmpReg ← #0;
  if evenSum = tmpReg then [
    evenSum ← #0
  ] else [
    evenSum ← #1
  ]
]

/-- Standard-basis Word-RAM program computing `#(hamPaths I.adj)` in `O((n³ + 1) · 2 ^ n)`
instructions. -/
def program : Program .standard 22 := countHamCode.program evenSum

/-- Standard-basis Word-RAM program deciding `(hamPaths I.adj).Nonempty` (`1` or `0`) in
`O((n³ + 1) · 2 ^ n)` instructions. -/
def decideProgram : Program .standard 22 := decideHamCode.program evenSum

/-! ## Shared vector and odometer lemmas -/

private def memAddrOK (I : Instance) (mem : ℕ → ℕ) : Prop :=
  (∀ u v : Fin I.n, mem (2 + u.1 * I.n + v.1) = if I.adj u v then 1 else 0)

private def vecFits (I : Instance) (w : ℕ) (base : ℕ) (mem : ℕ → ℕ) : Prop :=
  ∀ u : Fin I.n, Fits w (mem (base + u.1))

private theorem exec_copyVec {w : ℕ} (I : Instance) (srcReg dstReg : Fin 22)
    (srcBase dstBase : ℕ) (hsrc_ne : srcReg ≠ iReg ∧ srcReg ≠ addr1 ∧ srcReg ≠ tmpReg ∧
      srcReg ≠ addr2)
    (hdst_ne : dstReg ≠ iReg ∧ dstReg ≠ addr1 ∧ dstReg ≠ tmpReg ∧ dstReg ≠ addr2)
    (hdisj : ∀ u v : Fin I.n, dstBase + u.1 ≠ srcBase + v.1)
    (hfit : I.FitsWidth w)
    (haddr : Fits w (srcBase + I.n) ∧ Fits w (dstBase + I.n))
    (x : Data 22)
    (hx_n : x.regs nReg = I.n) (hx_1 : x.regs oneReg = 1)
    (hx_src : x.regs srcReg = srcBase) (hx_dst : x.regs dstReg = dstBase)
    (hv_fit : vecFits I w srcBase x.mem) :
    ∃ y, ExecWithin w (copyVec srcReg dstReg) x y (7 * I.n + 3) ∧
      (∀ u : Fin I.n, y.mem (dstBase + u.1) = x.mem (srcBase + u.1)) ∧
      (∀ a, ¬ (dstBase ≤ a ∧ a < dstBase + I.n) → y.mem a = x.mem a) ∧
      (∀ r : Fin 22, r ≠ iReg ∧ r ≠ addr1 ∧ r ≠ tmpReg ∧ r ≠ addr2 → y.regs r = x.regs r) := by
  have hn_fit : Fits w I.n := hfit.of_le (by
    have h1 := one_le_word_prod I.n
    unfold Instance.wordBound; nlinarith)
  have h0_fit : Fits w 0 := hfit.of_le (by unfold Instance.wordBound; omega)
  unfold copyVec
  let x1 : Data 22 := x.set iReg 0
  have hx1_ex : ExecWithin w (.op (.const iReg 0)) x x1 1 :=
    ExecWithin.const (B := .standard) h0_fit
  let Inv (i : ℕ) (d : Data 22) : Prop :=
    i ≤ I.n ∧ d.regs nReg = I.n ∧ d.regs oneReg = 1 ∧
    d.regs srcReg = srcBase ∧ d.regs dstReg = dstBase ∧
    (∀ u < i, d.mem (dstBase + u) = x.mem (srcBase + u)) ∧
    (∀ a, ¬ (dstBase ≤ a ∧ a < dstBase + i) → d.mem a = x.mem a)
  have hx1_inv : Inv (x1.regs iReg) x1 := by
    refine ⟨by wram_simp [x1]; exact Nat.zero_le _, ?_, ?_, ?_, ?_,
      fun u hu => by wram_simp [x1] at hu, fun a _ => rfl⟩
    · wram_simp [x1, hx_n]
    · wram_simp [x1, hx_1]
    · wram_simp [x1, hsrc_ne.1, hx_src]
    · wram_simp [x1, hdst_ne.1, hx_dst]
  have hx1_le : x1.regs iReg ≤ I.n := by wram_simp [x1]; exact Nat.zero_le _
  obtain ⟨y, hy, hy_inv, hy_i⟩ := ExecWithin.loop_count (w := w) (T := 5)
    (body := ram[
      addr1 ← srcReg + iReg;
      tmpReg ← *addr1;
      addr2 ← dstReg + iReg;
      *addr2 ← tmpReg;
      iReg ← iReg + oneReg ]) Inv (fun _ h => h.2.1)
    (fun d hInv hlt => by
      obtain ⟨hi_le, dn, d1, dsrc, ddst, hpre, hout⟩ := hInv
      have hi_lt : d.regs iReg < I.n := hlt
      have hf1 : Fits w (d.regs srcReg + d.regs iReg) := haddr.1.of_le (by rw [dsrc]; omega)
      have hf2 : Fits w (d.regs dstReg + d.regs iReg) := haddr.2.of_le (by rw [ddst]; omega)
      have hsrc_mem : d.mem (srcBase + d.regs iReg) = x.mem (srcBase + d.regs iReg) := by
        refine hout _ fun ⟨hlo, hhi⟩ => ?_
        have hlt_n : srcBase + d.regs iReg - dstBase < I.n := by omega
        exact hdisj ⟨srcBase + d.regs iReg - dstBase, hlt_n⟩ ⟨d.regs iReg, hi_lt⟩
          (by dsimp; omega)
      have htmp_fit : Fits w (d.mem (srcBase + d.regs iReg)) := by
        rw [hsrc_mem]; exact hv_fit ⟨d.regs iReg, hi_lt⟩
      have hf_i : Fits w (d.regs iReg + d.regs oneReg) := by
        rw [d1]; exact hn_fit.of_le (by omega)
      let z : Data 22 :=
        ((((d.set addr1 (srcBase + d.regs iReg)).set tmpReg
          (d.mem (srcBase + d.regs iReg))).set addr2 (dstBase + d.regs iReg)).write
          (dstBase + d.regs iReg) (d.mem (srcBase + d.regs iReg))).set
          iReg (d.regs iReg + 1)
      have hz_ex : ExecWithin w (ram[
          addr1 ← srcReg + iReg;
          tmpReg ← *addr1;
          addr2 ← dstReg + iReg;
          *addr2 ← tmpReg;
          iReg ← iReg + oneReg ]) d z 5 := by
        wram_exec [dsrc, ddst, d1]
      refine ⟨z, hz_ex, ⟨hi_lt, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · wram_simp [z, dn]
      · wram_simp [z, d1]
      · wram_simp [z, hsrc_ne.1, hsrc_ne.2.1, hsrc_ne.2.2.1, hsrc_ne.2.2.2, dsrc]
      · wram_simp [z, hdst_ne.1, hdst_ne.2.1, hdst_ne.2.2.1, hdst_ne.2.2.2, ddst]
      · intro u hu
        by_cases hui : u = d.regs iReg
        · subst hui
          wram_simp [z, Data.write, ddst, dsrc, Function.update_self, hsrc_mem]
        · have hupd := Function.update_of_ne (by omega : dstBase + u ≠ dstBase + d.regs iReg)
            (d.mem (srcBase + d.regs iReg)) d.mem
          simpa [z, Data.write, ddst, dsrc] using hupd.trans (hpre u (by omega))
      · intro a ha
        have hupd := Function.update_of_ne (by omega : a ≠ dstBase + d.regs iReg)
          (d.mem (srcBase + d.regs iReg)) d.mem
        simpa [z, Data.write, ddst, dsrc] using hupd.trans (hout a (by omega))
      · wram_simp [z])
    hx1_le hx1_inv
  refine ⟨y, (hx1_ex.seq (hy.mono (by
      have hx1_0 : x1.regs iReg = 0 := by wram_simp [x1]
      rw [hx1_0, Nat.sub_zero]))).mono (by omega),
    fun u => hy_inv.2.2.2.2.2.1 u.1 u.isLt, hy_inv.2.2.2.2.2.2, fun r hr => ?_⟩
  · have hloop_pres : (Code.loop (.lt iReg nReg) ram[
        addr1 ← srcReg + iReg; tmpReg ← *addr1; addr2 ← dstReg + iReg;
        *addr2 ← tmpReg; iReg ← iReg + oneReg ]).Preserves r := by
      simp only [Code.Preserves, Op.dest, Op.bin, ne_eq, Option.some.injEq]
      exact ⟨hr.2.1.symm, hr.2.2.1.symm, hr.2.2.2.symm, by simp, hr.1.symm⟩
    rw [hy.regs_eq hloop_pres]
    wram_simp [x1, hr.1]

private theorem exec_stepInnerCell {w : ℕ} (I : Instance) (k r : ℕ)
    (hfit : I.FitsWidth w) (hr : r < I.n - 1) (u : Fin I.n) (sv : Data 22)
    (hv_lt : sv.regs vReg < I.n)
    (svn : sv.regs nReg = I.n) (sv1 : sv.regs oneReg = 1) (svadj : sv.regs adjBase = 2)
    (svin : sv.regs inBase = 2 + I.n * I.n) (svcur : sv.regs curBase = 2 + I.n * I.n + I.n)
    (svnext : sv.regs nextBase = 2 + I.n * I.n + 2 * I.n) (svu : sv.regs uReg = u.1)
    (sva2 : sv.regs addr2 = 2 + u.1 * I.n)
    (d_adj : memAddrOK I sv.mem)
    (d_cur : ∀ v : Fin I.n, sv.mem (2 + I.n * I.n + I.n + v.1) =
      walkCountFrom I.adj (maskSet I.n k) r v)
    (svacc : sv.regs accReg = ∑ v : Fin I.n, if v.1 < sv.regs vReg ∧ I.adj u v then
      walkCountFrom I.adj (maskSet I.n k) r v else 0) :
    ∃ s', ExecWithin w (ram[
        addr1 ← addr2 + vReg;
        tmpReg ← *addr1;
        if tmpReg = oneReg then [
          addr1 ← curBase + vReg;
          tmpReg ← *addr1;
          accReg ← accReg + tmpReg
        ] else [
          tmpReg ← #0
        ];
        vReg ← vReg + oneReg ]) sv s' 8 ∧
      (sv.regs vReg + 1 ≤ I.n ∧ s'.regs nReg = I.n ∧ s'.regs oneReg = 1 ∧
        s'.regs adjBase = 2 ∧ s'.regs inBase = 2 + I.n * I.n ∧
        s'.regs curBase = 2 + I.n * I.n + I.n ∧ s'.regs nextBase = 2 + I.n * I.n + 2 * I.n ∧
        s'.regs uReg = u.1 ∧ s'.regs addr2 = 2 + u.1 * I.n ∧ s'.mem = sv.mem ∧
        s'.regs accReg = ∑ v : Fin I.n, if v.1 < sv.regs vReg + 1 ∧ I.adj u v then
          walkCountFrom I.adj (maskSet I.n k) r v else 0) ∧
      s'.regs vReg = sv.regs vReg + 1 := by
  have h1_le := one_le_word_prod I.n
  have hn_fit : Fits w I.n := hfit.of_le (by unfold Instance.wordBound; nlinarith)
  have h1_fit : Fits w 1 := hfit.of_le (by unfold Instance.wordBound; nlinarith)
  have haddr_bound : Fits w (2 + I.n * I.n + 3 * I.n) :=
    hfit.of_le (by unfold Instance.wordBound; nlinarith)
  have hpow_le : (I.n + 1) ^ (r + 1) ≤ (I.n + 1) ^ I.n :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hin_le : I.n ^ (r + 1) ≤ (I.n + 1) ^ I.n :=
    (Nat.pow_le_pow_left (Nat.le_succ I.n) _).trans hpow_le
  have hval_fit : Fits w ((I.n + 1) ^ I.n) := hfit.of_le (by
    unfold Instance.wordBound
    nlinarith [Nat.one_le_pow I.n 2 (by decide), Nat.one_le_pow I.n (I.n + 1) (by omega)])
  let v : Fin I.n := ⟨sv.regs vReg, hv_lt⟩
  have hf_va1 : Fits w (sv.regs addr2 + sv.regs vReg) := by
    rw [sva2]; exact haddr_bound.of_le (by have := adj_index_lt u v; omega)
  have hadj_read : sv.mem (2 + u.1 * I.n + v.1) = if I.adj u v then 1 else 0 := d_adj u v
  have htmp1_fit : Fits w (sv.mem (sv.regs addr2 + sv.regs vReg)) := by
    rw [sva2]; change Fits w (sv.mem (2 + u.1 * I.n + v.1)); rw [hadj_read]
    split_ifs <;> exact h1_fit.of_le (by decide)
  have hf_v1 : Fits w (sv.regs vReg + sv.regs oneReg) := by
    rw [sv1]; exact hn_fit.of_le (by omega)
  have hsplit : ∑ w' : Fin I.n, (if w'.1 < v.1 + 1 ∧ I.adj u w' then
      walkCountFrom I.adj (maskSet I.n k) r w' else 0) =
      (∑ w' : Fin I.n, if w'.1 < v.1 ∧ I.adj u w' then
        walkCountFrom I.adj (maskSet I.n k) r w' else 0) +
      if I.adj u v then walkCountFrom I.adj (maskSet I.n k) r v else 0 := by
    have heq : ∑ w' : Fin I.n, (if w' = v then
        if I.adj u v then walkCountFrom I.adj (maskSet I.n k) r v else 0 else 0) =
        if I.adj u v then walkCountFrom I.adj (maskSet I.n k) r v else 0 := by simp
    rw [← heq, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w' _ => ?_
    by_cases hwv : w' = v
    · subst hwv; simp
    · have hne : w'.1 ≠ v.1 := fun h => hwv (Fin.ext h)
      simp [hwv, show w'.1 < v.1 + 1 ↔ w'.1 < v.1 by omega]
  by_cases hadj : I.adj u v = true
  · have hf_cur_addr : Fits w (sv.regs curBase + sv.regs vReg) := by
      rw [svcur]; exact haddr_bound.of_le (by omega)
    have hcur_read : sv.mem (2 + I.n * I.n + I.n + v.1) =
        walkCountFrom I.adj (maskSet I.n k) r v := d_cur v
    have hcur_v_fit : Fits w (sv.mem (sv.regs curBase + sv.regs vReg)) := by
      rw [svcur]; change Fits w (sv.mem (2 + I.n * I.n + I.n + v.1)); rw [hcur_read]
      exact hval_fit.of_le ((walkCountFrom_le_pow I.adj _ r v).trans
        ((Nat.pow_le_pow_left (Nat.le_add_right I.n 1) r).trans
          ((Nat.pow_le_pow_right (by omega) (Nat.le_succ r)).trans hpow_le)))
    have hsum_step_le : sv.regs accReg +
        walkCountFrom I.adj (maskSet I.n k) r v ≤ (I.n + 1) ^ I.n := by
      rw [svacc]
      have hle_sum : (∑ w' : Fin I.n, if w'.1 < v.1 ∧ I.adj u w' then
          walkCountFrom I.adj (maskSet I.n k) r w' else 0) +
          walkCountFrom I.adj (maskSet I.n k) r v ≤
          ∑ w' : Fin I.n, walkCountFrom I.adj (maskSet I.n k) r w' := by
        rw [show walkCountFrom I.adj (maskSet I.n k) r v =
          if I.adj u v then walkCountFrom I.adj (maskSet I.n k) r v else 0 by
          simp [hadj], ← hsplit]
        refine Finset.sum_le_sum fun w' _ => ?_
        split_ifs <;> omega
      calc _ ≤ ∑ w' : Fin I.n, walkCountFrom I.adj (maskSet I.n k) r w' := hle_sum
        _ ≤ ∑ _w' : Fin I.n, I.n ^ r :=
            Finset.sum_le_sum fun w' _ => walkCountFrom_le_pow I.adj _ r w'
        _ = I.n * I.n ^ r := by simp
        _ = I.n ^ (r + 1) := by rw [← pow_succ']
        _ ≤ (I.n + 1) ^ I.n := hin_le
    have hf_acc_add :
        Fits w (sv.regs accReg + sv.mem (sv.regs curBase + sv.regs vReg)) := by
      rw [svcur]; change Fits w (sv.regs accReg + sv.mem (2 + I.n * I.n + I.n + v.1))
      rw [hcur_read]; exact hval_fit.of_le hsum_step_le
    have hadj1 : sv.mem (2 + u.1 * I.n + v.1) = 1 := by rw [hadj_read]; simp [hadj]
    have hcur_sv : sv.mem (2 + I.n * I.n + I.n + sv.regs vReg) =
        walkCountFrom I.adj (maskSet I.n k) r v := hcur_read
    refine (WP.seq ?_).exists_execWithin
    wram_exec [sva2, hadj1, svcur, hcur_read, sv1]
    refine ⟨⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    all_goals wram_simp [svn, sv1, svadj, svin, svcur, svnext, svu, sva2]
    · rw [svacc, hsplit, hcur_sv]; simp [hadj, v]
  · have hadj_f : I.adj u v = false := by cases hm : I.adj u v <;> simp_all
    have hadj0 : sv.mem (2 + u.1 * I.n + v.1) = 0 := by rw [hadj_read]; simp [hadj_f]
    refine (WP.seq ?_).exists_execWithin
    wram_exec [sva2, hadj0, sv1]
    refine ⟨⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    all_goals wram_simp [svn, sv1, svadj, svin, svcur, svnext, svu, sva2]
    · rw [svacc, hsplit]; simp [hadj_f, v]

private theorem exec_stepCellCode {w : ℕ} (I : Instance) (k r : ℕ)
    (hfit : I.FitsWidth w) (hr : r < I.n - 1) (x d : Data 22)
    (hlt : d.regs uReg < I.n)
    (dn : d.regs nReg = I.n) (d1 : d.regs oneReg = 1) (dadj : d.regs adjBase = 2)
    (din : d.regs inBase = 2 + I.n * I.n) (dcur : d.regs curBase = 2 + I.n * I.n + I.n)
    (dnext : d.regs nextBase = 2 + I.n * I.n + 2 * I.n)
    (d_adj : memAddrOK I d.mem)
    (d_in : ∀ u : Fin I.n, d.mem (2 + I.n * I.n + u.1) = if k.testBit u.1 then 1 else 0)
    (d_cur : ∀ u : Fin I.n, d.mem (2 + I.n * I.n + I.n + u.1) =
      walkCountFrom I.adj (maskSet I.n k) r u)
    (d_pre : ∀ u < d.regs uReg, ∀ hu : u < I.n,
      d.mem (2 + I.n * I.n + 2 * I.n + u) = walkCountFrom I.adj (maskSet I.n k) (r + 1) ⟨u, hu⟩)
    (d_out : ∀ a, ¬ (2 + I.n * I.n + 2 * I.n ≤ a ∧ a < 2 + I.n * I.n + 2 * I.n + d.regs uReg) →
      d.mem a = x.mem a) :
    ∃ z, ExecWithin w stepCellCode d z (10 * I.n + 13) ∧
      (d.regs uReg + 1 ≤ I.n ∧ z.regs nReg = I.n ∧ z.regs oneReg = 1 ∧ z.regs adjBase = 2 ∧
        z.regs inBase = 2 + I.n * I.n ∧ z.regs curBase = 2 + I.n * I.n + I.n ∧
        z.regs nextBase = 2 + I.n * I.n + 2 * I.n ∧ memAddrOK I z.mem ∧
        (∀ u : Fin I.n, z.mem (2 + I.n * I.n + u.1) = if k.testBit u.1 then 1 else 0) ∧
        (∀ u : Fin I.n, z.mem (2 + I.n * I.n + I.n + u.1) =
          walkCountFrom I.adj (maskSet I.n k) r u) ∧
        (∀ u < d.regs uReg + 1, ∀ hu : u < I.n,
          z.mem (2 + I.n * I.n + 2 * I.n + u) =
            walkCountFrom I.adj (maskSet I.n k) (r + 1) ⟨u, hu⟩) ∧
        (∀ a, ¬ (2 + I.n * I.n + 2 * I.n ≤ a ∧
          a < 2 + I.n * I.n + 2 * I.n + (d.regs uReg + 1)) → z.mem a = x.mem a)) ∧
      z.regs uReg = d.regs uReg + 1 := by
  have h1_le := one_le_word_prod I.n
  have hn_fit : Fits w I.n := hfit.of_le (by unfold Instance.wordBound; nlinarith)
  have h0_fit : Fits w 0 := hfit.of_le (by unfold Instance.wordBound; omega)
  have h1_fit : Fits w 1 := hfit.of_le (by unfold Instance.wordBound; omega)
  have haddr_bound : Fits w (2 + I.n * I.n + 3 * I.n) :=
    hfit.of_le (by unfold Instance.wordBound; nlinarith)
  have hpow_le : (I.n + 1) ^ (r + 1) ≤ (I.n + 1) ^ I.n :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hval_fit : Fits w ((I.n + 1) ^ I.n) :=
    hfit.of_le (by
      have h2n : 1 ≤ 2 ^ I.n := Nat.one_le_two_pow
      unfold Instance.wordBound; nlinarith)
  have hu_lt : d.regs uReg < I.n := hlt
  let u : Fin I.n := ⟨d.regs uReg, hu_lt⟩
  have hf_in : Fits w (d.regs inBase + d.regs uReg) :=
    haddr_bound.of_le (by rw [din]; omega)
  have hbit_eq : d.mem (2 + I.n * I.n + u.1) = if k.testBit u.1 then 1 else 0 := d_in u
  have hf_u_fit : Fits w (d.mem (d.regs inBase + d.regs uReg)) := by
    rw [din]; change Fits w (d.mem (2 + I.n * I.n + u.1)); rw [hbit_eq]
    split_ifs <;> exact h1_fit.of_le (by decide)
  have hf_next_addr : Fits w (d.regs nextBase + d.regs uReg) :=
    haddr_bound.of_le (by rw [dnext]; omega)
  have hf_u1 : Fits w (d.regs uReg + d.regs oneReg) := by
    rw [d1]; exact hn_fit.of_le (by omega)
  have hu_sum_le : walkCountFrom I.adj (maskSet I.n k) (r + 1) u ≤ I.n ^ (r + 1) :=
    walkCountFrom_le_pow I.adj (maskSet I.n k) (r + 1) u
  have hin_le : I.n ^ (r + 1) ≤ (I.n + 1) ^ I.n :=
    (Nat.pow_le_pow_left (Nat.le_succ I.n) (r + 1)).trans hpow_le
  have hf_row : Fits w (d.regs uReg * d.regs nReg) := by
    rw [dn]
    have : u.1 * I.n ≤ I.n * I.n := Nat.mul_le_mul_right _ hu_lt.le
    exact haddr_bound.of_le (by dsimp [u] at this; omega)
  have hf_adjBase : Fits w (d.regs adjBase + d.regs uReg * d.regs nReg) := by
    rw [dadj, dn]
    have : u.1 * I.n ≤ I.n * I.n := Nat.mul_le_mul_right _ hu_lt.le
    exact haddr_bound.of_le (by dsimp [u] at this; omega)
  have hf_u_val : Fits w (walkCountFrom I.adj (maskSet I.n k) (r + 1) u) :=
    hval_fit.of_le (hu_sum_le.trans hin_le)
  let d1' : Data 22 := d.set addr1 (2 + I.n * I.n + u.1)
  have hd1'_ex : ExecWithin w (.op (.bin .add addr1 inBase uReg)) d d1' 1 := by
    wram_exec [din]
  let d2' : Data 22 := d1'.set tmpReg (if k.testBit u.1 then 1 else 0)
  have hd2'_ex : ExecWithin w (.op (B := .standard) (.load tmpReg addr1)) d1' d2' 1 := by
    have haddr1 : d1'.regs addr1 = 2 + I.n * I.n + u.1 := by wram_simp [d1']
    have hbit1 : d1'.mem (2 + I.n * I.n + u.1) = if k.testBit u.1 then 1 else 0 := by
      wram_simp [d1']; exact hbit_eq
    have hfit1 : Fits w (d1'.mem (d1'.regs addr1)) := by
      wram_simp [d1', hbit_eq]
      exact h1_fit.of_le (by split_ifs <;> decide)
    wram_exec [haddr1, hbit1]
  have hbranch_post : ∃ z, ExecWithin w (ram[
      if tmpReg = oneReg then [
        accReg ← #0;
        vReg ← #0;
        addr2 ← uReg * nReg;
        addr2 ← adjBase + addr2;
        while vReg < nReg do [
          addr1 ← addr2 + vReg;
          tmpReg ← *addr1;
          if tmpReg = oneReg then [
            addr1 ← curBase + vReg;
            tmpReg ← *addr1;
            accReg ← accReg + tmpReg
          ] else [
            tmpReg ← #0
          ];
          vReg ← vReg + oneReg
        ]
      ] else [
        accReg ← #0
      ]]) d2' z (10 * I.n + 8) ∧
      z.mem = d.mem ∧
      z.regs nReg = I.n ∧ z.regs oneReg = 1 ∧ z.regs adjBase = 2 ∧
      z.regs inBase = 2 + I.n * I.n ∧ z.regs curBase = 2 + I.n * I.n + I.n ∧
      z.regs nextBase = 2 + I.n * I.n + 2 * I.n ∧ z.regs uReg = u.1 ∧
      z.regs accReg = walkCountFrom I.adj (maskSet I.n k) (r + 1) u := by
    by_cases hbit : k.testBit u.1 = true
    · have hcond : Cond.Holds (.eq tmpReg oneReg) d2' := by
        change d2'.regs tmpReg = d2'.regs oneReg
        wram_simp [d2', d1', d1, hbit]
      let s0a : Data 22 := d2'.set accReg 0
      let s0b : Data 22 := s0a.set vReg 0
      let s0c : Data 22 := s0b.set addr2 (d.regs uReg * I.n)
      let s0 : Data 22 := s0c.set addr2 (2 + d.regs uReg * I.n)
      have hs0a_ex : ExecWithin w (.op (.const accReg 0)) d2' s0a 1 :=
        ExecWithin.const (B := .standard) h0_fit
      have hs0b_ex : ExecWithin w (.op (.const vReg 0)) s0a s0b 1 :=
        ExecWithin.const (B := .standard) h0_fit
      have hs0c_ex : ExecWithin w (.op (.bin .mul addr2 uReg nReg)) s0b s0c 1 := by
        have h1 : s0b.regs uReg = d.regs uReg := by wram_simp [s0b, s0a, d2', d1']
        have h2 : s0b.regs nReg = I.n := by wram_simp [s0b, s0a, d2', d1', dn]
        rw [dn] at hf_row
        wram_exec [h1, h2]
      have hs0d_ex : ExecWithin w (.op (.bin .add addr2 adjBase addr2)) s0c s0 1 := by
        have h1 : s0c.regs adjBase = 2 := by wram_simp [s0c, s0b, s0a, d2', d1', dadj]
        have h2 : s0c.regs addr2 = d.regs uReg * I.n := by wram_simp [s0c]
        rw [dadj, dn] at hf_adjBase
        wram_exec [h1, h2]
      let InvV (vIdx : ℕ) (s : Data 22) : Prop :=
        vIdx ≤ I.n ∧ s.regs nReg = I.n ∧ s.regs oneReg = 1 ∧
        s.regs adjBase = 2 ∧ s.regs inBase = 2 + I.n * I.n ∧
        s.regs curBase = 2 + I.n * I.n + I.n ∧
        s.regs nextBase = 2 + I.n * I.n + 2 * I.n ∧
        s.regs uReg = u.1 ∧ s.regs addr2 = 2 + u.1 * I.n ∧ s.mem = d.mem ∧
        s.regs accReg = ∑ v : Fin I.n, if v.1 < vIdx ∧ I.adj u v then
          walkCountFrom I.adj (maskSet I.n k) r v else 0
      have hs0_inv : InvV (s0.regs vReg) s0 := by
        refine ⟨by wram_simp [s0, s0c, s0b]; exact Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          ?_, rfl, ?_⟩
        · wram_simp [s0, s0c, s0b, s0a, d2', d1', dn]
        · wram_simp [s0, s0c, s0b, s0a, d2', d1', d1]
        · wram_simp [s0, s0c, s0b, s0a, d2', d1', dadj]
        · wram_simp [s0, s0c, s0b, s0a, d2', d1', din]
        · wram_simp [s0, s0c, s0b, s0a, d2', d1', dcur]
        · wram_simp [s0, s0c, s0b, s0a, d2', d1', dnext]
        · wram_simp [s0, s0c, s0b, s0a, d2', d1']; rfl
        · wram_simp [s0]; rfl
        · wram_simp [s0, s0c, s0b, s0a]; exact (Finset.sum_eq_zero fun _ _ => by simp).symm
      have hs0_le : s0.regs vReg ≤ I.n := by wram_simp [s0, s0c, s0b]; exact Nat.zero_le _
      obtain ⟨s1', hs1', hs1'_inv, _⟩ := ExecWithin.loop_count (w := w) (T := 8)
        (body := ram[
          addr1 ← addr2 + vReg;
          tmpReg ← *addr1;
          if tmpReg = oneReg then [
            addr1 ← curBase + vReg;
            tmpReg ← *addr1;
            accReg ← accReg + tmpReg
          ] else [
            tmpReg ← #0
          ];
          vReg ← vReg + oneReg ]) InvV (fun _ h => h.2.1)
        (fun sv hsv hv_lt => by
          obtain ⟨_, svn, sv1, svadj, svin, svcur, svnext, svu, sva2, svm, svacc⟩ := hsv
          have hadjm : memAddrOK I sv.mem := svm ▸ d_adj
          have hcurm : ∀ v : Fin I.n, sv.mem (2 + I.n * I.n + I.n + v.1) =
              walkCountFrom I.adj (maskSet I.n k) r v := svm ▸ d_cur
          obtain ⟨s', hs', ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩, h12⟩ :=
            exec_stepInnerCell I k r hfit hr u sv hv_lt svn sv1 svadj svin svcur svnext svu
              sva2 hadjm hcurm svacc
          exact ⟨s', hs', ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10.trans svm, h11⟩, h12⟩) hs0_le
          hs0_inv
      have hs1'_v : s0.regs vReg = 0 := by wram_simp [s0, s0c, s0b]
      rw [hs1'_v, Nat.sub_zero] at hs1'
      have hs1'_time : ExecWithin w (Code.loop (.lt vReg nReg) ram[
          addr1 ← addr2 + vReg;
          tmpReg ← *addr1;
          if tmpReg = oneReg then [
            addr1 ← curBase + vReg;
            tmpReg ← *addr1;
            accReg ← accReg + tmpReg
          ] else [
            tmpReg ← #0
          ];
          vReg ← vReg + oneReg ]) s0 s1' (10 * I.n + 2) :=
        hs1'.mono (by ring_nf; exact le_rfl)
      obtain ⟨_, s1n, s11, s1adj, s1in, s1cur, s1next, s1u, _, s1m, s1acc⟩ := hs1'_inv
      have hbody_ex := hs0a_ex.seq (hs0b_ex.seq (hs0c_ex.seq (hs0d_ex.seq hs1'_time)))
      refine ⟨s1', (ExecWithin.branch_pos hcond hbody_ex).mono (by omega),
        s1m, s1n, s11, s1adj, s1in, s1cur, s1next, s1u, ?_⟩
      rw [s1acc, walkCountFrom]
      refine Finset.sum_congr rfl fun v _ => ?_
      have hu_in : u ∈ maskSet I.n k := mem_maskSet.2 hbit
      simp [hu_in, v.isLt]
    · have hbit_f : k.testBit u.1 = false := by cases hm : k.testBit u.1 <;> simp_all
      have hcond : ¬ Cond.Holds (.eq tmpReg oneReg) d2' := by
        change d2'.regs tmpReg ≠ d2'.regs oneReg
        wram_simp [d2', d1', d1, hbit_f]
        decide
      let z0 : Data 22 := d2'.set accReg 0
      have hz0_ex : ExecWithin w (.op (.const accReg 0)) d2' z0 1 :=
        ExecWithin.const (B := .standard) h0_fit
      refine ⟨z0, (ExecWithin.branch_neg hcond hz0_ex).mono (by omega),
        rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · wram_simp [z0, d2', d1', dn]
      · wram_simp [z0, d2', d1', d1]
      · wram_simp [z0, d2', d1', dadj]
      · wram_simp [z0, d2', d1', din]
      · wram_simp [z0, d2', d1', dcur]
      · wram_simp [z0, d2', d1', dnext]
      · wram_simp [z0, d2', d1']; rfl
      · wram_simp [z0]
        rw [walkCountFrom]
        have hu_nin : u ∉ maskSet I.n k := by simp [mem_maskSet, hbit_f]
        exact (Finset.sum_eq_zero fun v _ => by simp [hu_nin]).symm
  obtain ⟨z, hz_ex, hz_m, zn, z1, zadj, zin, zcur, znext, zu, zacc⟩ := hbranch_post
  let z2 : Data 22 :=
    ((z.set addr1 (2 + I.n * I.n + 2 * I.n + u.1)).write
      (2 + I.n * I.n + 2 * I.n + u.1) (walkCountFrom I.adj (maskSet I.n k) (r + 1) u)).set
      uReg (u.1 + 1)
  have hz2_ex : ExecWithin w
      ram[ addr1 ← nextBase + uReg; *addr1 ← accReg; uReg ← uReg + oneReg ] z z2 3 := by
    have hzf_next : Fits w (z.regs nextBase + z.regs uReg) := by
      rw [znext, zu, ← dnext]; exact hf_next_addr
    have hzf_u_val : Fits w (z.regs accReg) := by rw [zacc]; exact hf_u_val
    have hzf_u1 : Fits w (z.regs uReg + z.regs oneReg) := by
      rw [zu, z1, ← d1]; exact hf_u1
    wram_exec [znext, zu, zacc, z1]
  unfold stepCellCode
  refine ⟨z2, (hd1'_ex.seq (hd2'_ex.seq (hz_ex.seq hz2_ex))).mono (by omega),
    ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · wram_simp [z2, zn]
  · wram_simp [z2, z1]
  · wram_simp [z2, zadj]
  · wram_simp [z2, zin]
  · wram_simp [z2, zcur]
  · wram_simp [z2, znext]
  · intro u' v'
    have hne : 2 + u'.1 * I.n + v'.1 ≠ 2 + I.n * I.n + 2 * I.n + u.1 := by
      have := adj_index_lt u' v'; omega
    wram_simp [z2, Data.write, Function.update_of_ne hne, hz_m]
    exact d_adj u' v'
  · intro u'
    have hne : 2 + I.n * I.n + u'.1 ≠ 2 + I.n * I.n + 2 * I.n + u.1 := by omega
    wram_simp [z2, Data.write, Function.update_of_ne hne, hz_m]
    exact d_in u'
  · intro u'
    have hne : 2 + I.n * I.n + I.n + u'.1 ≠ 2 + I.n * I.n + 2 * I.n + u.1 := by omega
    wram_simp [z2, Data.write, Function.update_of_ne hne, hz_m]
    exact d_cur u'
  · intro u' hu' hu'_lt
    by_cases heq : u' = u.1
    · subst heq
      wram_simp [z2, Data.write, Function.update_self]
    · have hne : 2 + I.n * I.n + 2 * I.n + u' ≠ 2 + I.n * I.n + 2 * I.n + u.1 := by omega
      wram_simp [z2, Data.write, Function.update_of_ne hne, hz_m]
      exact d_pre u' (by dsimp [u] at hu' heq; omega) hu'_lt
  · intro a ha
    have hne : a ≠ 2 + I.n * I.n + 2 * I.n + u.1 := by dsimp [u] at ha ⊢; omega
    wram_simp [z2, Data.write, Function.update_of_ne hne, hz_m]
    exact d_out a (by omega)
  · wram_simp [z2]; rfl

private theorem exec_stepVecCode {w : ℕ} (I : Instance) (k r : ℕ)
    (hfit : I.FitsWidth w) (hr : r < I.n - 1)
    (x : Data 22)
    (hx_n : x.regs nReg = I.n) (hx_1 : x.regs oneReg = 1) (hx_adj : x.regs adjBase = 2)
    (hx_in : x.regs inBase = 2 + I.n * I.n)
    (hx_cur : x.regs curBase = 2 + I.n * I.n + I.n)
    (hx_next : x.regs nextBase = 2 + I.n * I.n + 2 * I.n)
    (hmem_adj : memAddrOK I x.mem)
    (hmem_in : ∀ u : Fin I.n, x.mem (2 + I.n * I.n + u.1) = if k.testBit u.1 then 1 else 0)
    (hmem_cur : ∀ u : Fin I.n, x.mem (2 + I.n * I.n + I.n + u.1) =
      walkCountFrom I.adj (maskSet I.n k) r u) :
    ∃ y, ExecWithin w stepVecCode x y (I.n * (10 * I.n + 15) + 3) ∧
      (∀ u : Fin I.n, y.mem (2 + I.n * I.n + 2 * I.n + u.1) =
        walkCountFrom I.adj (maskSet I.n k) (r + 1) u) ∧
      (∀ a, ¬ (2 + I.n * I.n + 2 * I.n ≤ a ∧ a < 2 + I.n * I.n + 3 * I.n) →
        y.mem a = x.mem a) ∧
      (∀ reg : Fin 22, reg ≠ uReg ∧ reg ≠ vReg ∧ reg ≠ accReg ∧ reg ≠ addr1 ∧ reg ≠ addr2 ∧
        reg ≠ tmpReg → y.regs reg = x.regs reg) := by
  have h0_fit : Fits w 0 := hfit.of_le (by
    have h1_le := one_le_word_prod I.n
    unfold Instance.wordBound; omega)
  unfold stepVecCode
  let x1 : Data 22 := x.set uReg 0
  have hx1_ex : ExecWithin w (.op (.const uReg 0)) x x1 1 :=
    ExecWithin.const (B := .standard) h0_fit
  let InvU (uIdx : ℕ) (d : Data 22) : Prop :=
    uIdx ≤ I.n ∧
    d.regs nReg = I.n ∧ d.regs oneReg = 1 ∧ d.regs adjBase = 2 ∧
    d.regs inBase = 2 + I.n * I.n ∧ d.regs curBase = 2 + I.n * I.n + I.n ∧
    d.regs nextBase = 2 + I.n * I.n + 2 * I.n ∧
    memAddrOK I d.mem ∧
    (∀ u : Fin I.n, d.mem (2 + I.n * I.n + u.1) = if k.testBit u.1 then 1 else 0) ∧
    (∀ u : Fin I.n, d.mem (2 + I.n * I.n + I.n + u.1) =
      walkCountFrom I.adj (maskSet I.n k) r u) ∧
    (∀ u < uIdx, ∀ hu : u < I.n,
      d.mem (2 + I.n * I.n + 2 * I.n + u) =
        walkCountFrom I.adj (maskSet I.n k) (r + 1) ⟨u, hu⟩) ∧
    (∀ a, ¬ (2 + I.n * I.n + 2 * I.n ≤ a ∧ a < 2 + I.n * I.n + 2 * I.n + uIdx) →
      d.mem a = x.mem a)
  have hx1_inv : InvU (x1.regs uReg) x1 := by
    refine ⟨by wram_simp [x1]; exact Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      fun u hu => by wram_simp [x1] at hu, fun a _ => rfl⟩
    · wram_simp [x1, hx_n]
    · wram_simp [x1, hx_1]
    · wram_simp [x1, hx_adj]
    · wram_simp [x1, hx_in]
    · wram_simp [x1, hx_cur]
    · wram_simp [x1, hx_next]
    · exact hmem_adj
    · exact hmem_in
    · exact hmem_cur
  have hx1_le : x1.regs uReg ≤ I.n := by wram_simp [x1]; exact Nat.zero_le _
  obtain ⟨y, hy, hy_inv, _⟩ := ExecWithin.loop_count (w := w) (T := 10 * I.n + 13)
    (body := stepCellCode) InvU (fun _ h => h.2.1)
    (fun d hd hlt => by
      obtain ⟨_, dn, d1, dadj, din, dcur, dnext, d_adj, d_in, d_cur, d_pre, d_out⟩ := hd
      exact exec_stepCellCode I k r hfit hr x d hlt dn d1 dadj din dcur dnext d_adj d_in
        d_cur d_pre d_out)
    hx1_le hx1_inv
  have hy_time : ExecWithin w (Code.loop (.lt uReg nReg) stepCellCode) x1 y
      (I.n * (10 * I.n + 15) + 2) := by
    refine hy.mono ?_
    have hx1_0 : x1.regs uReg = 0 := by wram_simp [x1]
    rw [hx1_0, Nat.sub_zero]
  refine ⟨y, (hx1_ex.seq hy_time).mono (by omega),
    fun u => hy_inv.2.2.2.2.2.2.2.2.2.2.1 u.1 u.isLt u.isLt,
    fun a ha => hy_inv.2.2.2.2.2.2.2.2.2.2.2 a (by omega),
    fun reg hreg => ?_⟩
  · have hloop_pres : (Code.loop (.lt uReg nReg) stepCellCode).Preserves reg := by
      simp only [Code.Preserves, stepCellCode, Op.dest, Op.bin, ne_eq, Option.some.injEq]
      refine ⟨hreg.2.2.2.1.symm, hreg.2.2.2.2.2.symm, ⟨?_, hreg.2.2.1.symm⟩,
        hreg.2.2.2.1.symm, by simp, hreg.1.symm⟩
      refine ⟨hreg.2.2.1.symm, hreg.2.1.symm, hreg.2.2.2.2.1.symm, hreg.2.2.2.2.1.symm,
        ⟨hreg.2.2.2.1.symm, hreg.2.2.2.2.2.symm, ?_, hreg.2.1.symm⟩⟩
      refine ⟨⟨hreg.2.2.2.1.symm, hreg.2.2.2.2.2.symm, hreg.2.2.1.symm⟩, hreg.2.2.2.2.2.symm⟩
    rw [hy.regs_eq hloop_pres]
    wram_simp [x1, hreg.1]

private theorem stepCellCode_preserves {reg : Fin 22}
    (hreg : reg ≠ uReg ∧ reg ≠ vReg ∧ reg ≠ accReg ∧ reg ≠ addr1 ∧ reg ≠ addr2 ∧
      reg ≠ tmpReg) : stepCellCode.Preserves reg := by
  simp only [Code.Preserves, stepCellCode, Op.dest, Op.bin, ne_eq, Option.some.injEq]
  refine ⟨hreg.2.2.2.1.symm, hreg.2.2.2.2.2.symm, ⟨?_, hreg.2.2.1.symm⟩,
    hreg.2.2.2.1.symm, by simp, hreg.1.symm⟩
  refine ⟨hreg.2.2.1.symm, hreg.2.1.symm, hreg.2.2.2.2.1.symm, hreg.2.2.2.2.1.symm,
    ⟨hreg.2.2.2.1.symm, hreg.2.2.2.2.2.symm, ?_, hreg.2.1.symm⟩⟩
  refine ⟨⟨hreg.2.2.2.1.symm, hreg.2.2.2.2.2.symm, hreg.2.2.1.symm⟩, hreg.2.2.2.2.2.symm⟩

private theorem stepVecCode_preserves {reg : Fin 22}
    (hreg : reg ≠ uReg ∧ reg ≠ vReg ∧ reg ≠ accReg ∧ reg ≠ addr1 ∧ reg ≠ addr2 ∧
      reg ≠ tmpReg) : stepVecCode.Preserves reg := by
  simp only [Code.Preserves, stepVecCode, Op.dest, ne_eq, Option.some.injEq]
  refine ⟨hreg.1.symm, stepCellCode_preserves hreg⟩

private theorem copyVec_preserves {s d reg : Fin 22}
    (hreg : reg ≠ iReg ∧ reg ≠ addr1 ∧ reg ≠ tmpReg ∧ reg ≠ addr2) :
    (copyVec s d).Preserves reg := by
  simp only [Code.Preserves, copyVec, Op.dest, Op.bin, ne_eq, Option.some.injEq]
  refine ⟨hreg.1.symm, hreg.2.1.symm, hreg.2.2.1.symm, hreg.2.2.2.symm, by simp, hreg.1.symm⟩

private theorem adj_lt_inBase {n : ℕ} (u v : Fin n) : 2 + u.1 * n + v.1 < 2 + n * n := by
  have := adj_index_lt u v
  omega

private theorem rounds_out_left {n a : ℕ}
    (ha : ¬ (2 + n * n + n ≤ a ∧ a < 2 + n * n + 3 * n)) :
    ¬ (2 + n * n + n ≤ a ∧ a < 2 + n * n + n + n) := fun h =>
  ha ⟨h.1, by omega⟩

private theorem rounds_out_right {n a : ℕ}
    (ha : ¬ (2 + n * n + n ≤ a ∧ a < 2 + n * n + 3 * n)) :
    ¬ (2 + n * n + 2 * n ≤ a ∧ a < 2 + n * n + 3 * n) := fun h =>
  ha ⟨by omega, h.2⟩

private theorem exec_roundsCode {w : ℕ} (I : Instance) (k : ℕ) (hfit : I.FitsWidth w)
    (hn : 0 < I.n) (x : Data 22)
    (hx_n : x.regs nReg = I.n) (hx_nm1 : x.regs nMinus1 = I.n - 1)
    (hx_1 : x.regs oneReg = 1) (hx_adj : x.regs adjBase = 2)
    (hx_in : x.regs inBase = 2 + I.n * I.n)
    (hx_cur : x.regs curBase = 2 + I.n * I.n + I.n)
    (hx_next : x.regs nextBase = 2 + I.n * I.n + 2 * I.n)
    (hmem_adj : memAddrOK I x.mem)
    (hmem_in : ∀ u : Fin I.n, x.mem (2 + I.n * I.n + u.1) = if k.testBit u.1 then 1 else 0)
    (hmem_cur : ∀ u : Fin I.n, x.mem (2 + I.n * I.n + I.n + u.1) =
      walkCountFrom I.adj (maskSet I.n k) 0 u) :
    ∃ y, ExecWithin w roundsCode x y
        ((I.n - 1) * (I.n * (10 * I.n + 15) + 7 * I.n + 9) + 3) ∧
      (∀ u : Fin I.n, y.mem (2 + I.n * I.n + I.n + u.1) =
        walkCountFrom I.adj (maskSet I.n k) (I.n - 1) u) ∧
      (∀ a, ¬ (2 + I.n * I.n + I.n ≤ a ∧ a < 2 + I.n * I.n + 3 * I.n) →
        y.mem a = x.mem a) ∧
      (∀ reg : Fin 22, reg ≠ rReg ∧ reg ≠ iReg ∧ reg ≠ uReg ∧ reg ≠ vReg ∧ reg ≠ accReg ∧
        reg ≠ addr1 ∧ reg ≠ addr2 ∧ reg ≠ tmpReg → y.regs reg = x.regs reg) := by
  have h1_le := one_le_word_prod I.n
  have hn_fit : Fits w I.n := hfit.of_le (by unfold Instance.wordBound; nlinarith)
  have h0_fit : Fits w 0 := hfit.of_le (by unfold Instance.wordBound; omega)
  have haddr_bound : Fits w (2 + I.n * I.n + 3 * I.n) :=
    hfit.of_le (by unfold Instance.wordBound; nlinarith)
  have hval_fit : Fits w ((I.n + 1) ^ I.n) :=
    hfit.of_le (by
      have h2n : 1 ≤ 2 ^ I.n := Nat.one_le_two_pow
      unfold Instance.wordBound; nlinarith)
  unfold roundsCode
  let x1 : Data 22 := x.set rReg 0
  have hx1_ex : ExecWithin w (.op (.const rReg 0)) x x1 1 :=
    ExecWithin.const (B := .standard) h0_fit
  let InvR (r : ℕ) (d : Data 22) : Prop :=
    r ≤ I.n - 1 ∧
    d.regs nReg = I.n ∧ d.regs nMinus1 = I.n - 1 ∧ d.regs oneReg = 1 ∧
    d.regs adjBase = 2 ∧ d.regs inBase = 2 + I.n * I.n ∧
    d.regs curBase = 2 + I.n * I.n + I.n ∧ d.regs nextBase = 2 + I.n * I.n + 2 * I.n ∧
    memAddrOK I d.mem ∧
    (∀ u : Fin I.n, d.mem (2 + I.n * I.n + u.1) = if k.testBit u.1 then 1 else 0) ∧
    (∀ u : Fin I.n, d.mem (2 + I.n * I.n + I.n + u.1) =
      walkCountFrom I.adj (maskSet I.n k) r u) ∧
    (∀ a, ¬ (2 + I.n * I.n + I.n ≤ a ∧ a < 2 + I.n * I.n + 3 * I.n) → d.mem a = x.mem a)
  have hx1_inv : InvR (x1.regs rReg) x1 := by
    refine ⟨Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hmem_adj, hmem_in, ?_, fun _ _ => rfl⟩
    · wram_simp [x1, hx_n]
    · wram_simp [x1, hx_nm1]
    · wram_simp [x1, hx_1]
    · wram_simp [x1, hx_adj]
    · wram_simp [x1, hx_in]
    · wram_simp [x1, hx_cur]
    · wram_simp [x1, hx_next]
    · wram_simp [x1]; exact hmem_cur
  have hx1_le : x1.regs rReg ≤ I.n - 1 := by wram_simp [x1]; exact Nat.zero_le _
  obtain ⟨y, hy, hy_inv, _⟩ := ExecWithin.loop_count (w := w)
    (T := I.n * (10 * I.n + 15) + 7 * I.n + 7)
    (body := ram[ ⟪stepVecCode⟫; ⟪copyVec nextBase curBase⟫; rReg ← rReg + oneReg ])
    InvR (fun _ h => h.2.2.1)
    (fun d hd hlt => by
      obtain ⟨hr_le, dn, dnm1, d1, dadj, din, dcur, dnext, d_adj, d_in, d_cur, d_out⟩ := hd
      have hr_lt : d.regs rReg < I.n - 1 := hlt
      obtain ⟨s1, hs1, s1_next, s1_out, s1_regs⟩ := exec_stepVecCode I k (d.regs rReg) hfit hr_lt d
        dn d1 dadj din dcur dnext d_adj d_in d_cur
      have s1_adj : memAddrOK I s1.mem := fun u v => by
        rw [s1_out _ (by have := adj_index_lt u v; omega)]
        exact d_adj u v
      have s1_in : ∀ u : Fin I.n, s1.mem (2 + I.n * I.n + u.1) = if k.testBit u.1 then 1 else 0 :=
        fun u => by rw [s1_out _ (by omega)]; exact d_in u
      have s1_vfit : vecFits I w (2 + I.n * I.n + 2 * I.n) s1.mem := fun u => by
        rw [s1_next u]
        have h1 := walkCountFrom_le_pow I.adj (maskSet I.n k) (d.regs rReg + 1) u
        have h2 : I.n ^ (d.regs rReg + 1) ≤ (I.n + 1) ^ I.n :=
          (Nat.pow_le_pow_left (Nat.le_succ _) _).trans (Nat.pow_le_pow_right (by omega) (by omega))
        exact hval_fit.of_le (h1.trans h2)
      obtain ⟨s2, hs2, s2_cur, s2_out, s2_regs⟩ := exec_copyVec I nextBase curBase
        (2 + I.n * I.n + 2 * I.n) (2 + I.n * I.n + I.n) (by decide) (by decide)
        (fun u v => by omega) hfit ⟨haddr_bound.of_le (by omega), haddr_bound.of_le (by omega)⟩ s1
        ((s1_regs nReg (by decide)).trans dn) ((s1_regs oneReg (by decide)).trans d1)
        ((s1_regs nextBase (by decide)).trans dnext) ((s1_regs curBase (by decide)).trans dcur)
        s1_vfit
      have hs2_r : s2.regs rReg = d.regs rReg :=
        (s2_regs rReg (by decide)).trans (s1_regs rReg (by decide))
      have hs2_1 : s2.regs oneReg = 1 :=
        (s2_regs oneReg (by decide)).trans ((s1_regs oneReg (by decide)).trans d1)
      have hf_r1 : Fits w (s2.regs rReg + s2.regs oneReg) := by
        rw [hs2_r, hs2_1]
        exact hn_fit.of_le (Nat.le_trans hr_lt (Nat.sub_le _ _))
      have hs3_ex : ∃ s3, ExecWithin w (.op (.bin .add rReg rReg oneReg)) s2 s3 1 ∧
          s3 = s2.set rReg (d.regs rReg + 1) := by
        wram_exec [hs2_r, hs2_1]; rfl
      obtain ⟨s3, hs3, rfl⟩ := hs3_ex
      refine ⟨s2.set rReg (d.regs rReg + 1), (hs1.seq (hs2.seq hs3)).mono (by omega),
        ⟨hr_lt, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · wram_simp [(s2_regs nReg (by decide)).trans ((s1_regs nReg (by decide)).trans dn)]
      · wram_simp [(s2_regs nMinus1 (by decide)).trans ((s1_regs nMinus1 (by decide)).trans dnm1)]
      · wram_simp [hs2_1]
      · wram_simp [(s2_regs adjBase (by decide)).trans ((s1_regs adjBase (by decide)).trans dadj)]
      · wram_simp [(s2_regs inBase (by decide)).trans ((s1_regs inBase (by decide)).trans din)]
      · wram_simp [(s2_regs curBase (by decide)).trans ((s1_regs curBase (by decide)).trans dcur)]
      · wram_simp
          [(s2_regs nextBase (by decide)).trans ((s1_regs nextBase (by decide)).trans dnext)]
      · intro u v
        have hnot : ¬ (2 + I.n * I.n + I.n ≤ 2 + u.1 * I.n + v.1 ∧
            2 + u.1 * I.n + v.1 < 2 + I.n * I.n + I.n + I.n) := fun ⟨hlo, _⟩ =>
          Nat.not_le_of_gt (adj_lt_inBase u v)
            (le_trans (Nat.le_add_right (2 + I.n * I.n) I.n) hlo)
        have hmem_eq : s2.mem (2 + u.1 * I.n + v.1) = s1.mem (2 + u.1 * I.n + v.1) :=
          s2_out _ hnot
        wram_simp [Data.set, hmem_eq, s1_adj u v]
      · intro u
        have hu_lt := u.isLt
        have ha2 : s2.mem (2 + I.n * I.n + u.1) = s1.mem (2 + I.n * I.n + u.1) :=
          s2_out _ (by omega)
        wram_simp [Data.set, ha2, s1_in u]
      · intro u
        wram_simp [Data.set, s2_cur u, s1_next u]
      · intro a ha
        have ha2 : s2.mem a = s1.mem a := s2_out a (rounds_out_left ha)
        have ha1 : s1.mem a = d.mem a := s1_out a (rounds_out_right ha)
        change s2.mem a = x.mem a
        rw [ha2, ha1, d_out a ha]
      · wram_simp)
    hx1_le hx1_inv
  have hy_time : ExecWithin w (Code.loop (.lt rReg nMinus1)
      ram[ ⟪stepVecCode⟫; ⟪copyVec nextBase curBase⟫; rReg ← rReg + oneReg ]) x1 y
      ((I.n - 1) * (I.n * (10 * I.n + 15) + 7 * I.n + 9) + 2) := by
    refine hy.mono ?_
    have hx1_0 : x1.regs rReg = 0 := by wram_simp [x1]
    rw [hx1_0, Nat.sub_zero]
  refine ⟨y, (hx1_ex.seq hy_time).mono (by omega),
    hy_inv.2.2.2.2.2.2.2.2.2.2.1, hy_inv.2.2.2.2.2.2.2.2.2.2.2, fun reg hreg => ?_⟩
  · have hloop_pres : (Code.loop (.lt rReg nMinus1)
        ram[ ⟪stepVecCode⟫; ⟪copyVec nextBase curBase⟫; rReg ← rReg + oneReg ]).Preserves reg := by
      refine ⟨stepVecCode_preserves ⟨hreg.2.2.1, hreg.2.2.2.1, hreg.2.2.2.2.1, hreg.2.2.2.2.2.1,
          hreg.2.2.2.2.2.2.1, hreg.2.2.2.2.2.2.2⟩,
        copyVec_preserves ⟨hreg.2.1, hreg.2.2.2.2.2.1, hreg.2.2.2.2.2.2.2,
          hreg.2.2.2.2.2.2.1⟩,
        ?_⟩
      simpa only [Code.Preserves, Op.dest_bin, ne_eq, Option.some.injEq] using hreg.1.symm
    rw [hy.regs_eq hloop_pres]
    exact Data.set_regs_of_ne hreg.1 0

private theorem totalWalkCount_eq_sum {n : ℕ} (hn : 0 < n) (adj : Fin n → Fin n → Bool)
    (S : Finset (Fin n)) :
    totalWalkCount adj S = ∑ u : Fin n, walkCountFrom adj S (n - 1) u := by
  cases n with
  | zero => omega
  | succ m => rfl

private theorem totalWalkCount_zero {n : ℕ} (hn : n = 0) (adj : Fin n → Fin n → Bool)
    (S : Finset (Fin n)) :
    totalWalkCount adj S = 1 := by
  subst hn; rfl

private theorem exec_sumVecCode {w : ℕ} (I : Instance) (k : ℕ) (hfit : I.FitsWidth w)
    (hn : 0 < I.n) (x : Data 22)
    (hx_n : x.regs nReg = I.n) (hx_1 : x.regs oneReg = 1)
    (hx_cur : x.regs curBase = 2 + I.n * I.n + I.n)
    (hmem_cur : ∀ u : Fin I.n, x.mem (2 + I.n * I.n + I.n + u.1) =
      walkCountFrom I.adj (maskSet I.n k) (I.n - 1) u) :
    ∃ y, ExecWithin w sumVecCode x y (6 * I.n + 4) ∧
      y.mem = x.mem ∧ y.regs accReg = totalWalkCount I.adj (maskSet I.n k) ∧
      (∀ reg : Fin 22, reg ≠ iReg ∧ reg ≠ accReg ∧ reg ≠ addr1 ∧ reg ≠ tmpReg →
        y.regs reg = x.regs reg) := by
  have h1_le := one_le_word_prod I.n
  have hn_fit : Fits w I.n := hfit.of_le (by unfold Instance.wordBound; nlinarith)
  have h0_fit : Fits w 0 := hfit.of_le (by unfold Instance.wordBound; omega)
  have haddr_bound : Fits w (2 + I.n * I.n + 3 * I.n) :=
    hfit.of_le (by unfold Instance.wordBound; nlinarith)
  have hval_fit : Fits w ((I.n + 1) ^ I.n) :=
    hfit.of_le (by
      have h2n : 1 ≤ 2 ^ I.n := Nat.one_le_two_pow
      unfold Instance.wordBound; nlinarith)
  unfold sumVecCode
  let x0 : Data 22 := x.set accReg 0
  have hx0_ex : ExecWithin w (.op (.const accReg 0)) x x0 1 :=
    ExecWithin.const (B := .standard) h0_fit
  let x1 : Data 22 := x0.set iReg 0
  have hx1_ex : ExecWithin w (.op (.const iReg 0)) x0 x1 1 :=
    ExecWithin.const (B := .standard) h0_fit
  let InvS (i : ℕ) (d : Data 22) : Prop :=
    i ≤ I.n ∧ d.regs nReg = I.n ∧ d.regs oneReg = 1 ∧ d.regs curBase = 2 + I.n * I.n + I.n ∧
    d.mem = x.mem ∧
    d.regs accReg = ∑ u : Fin I.n, if u.1 < i then
      walkCountFrom I.adj (maskSet I.n k) (I.n - 1) u else 0
  have hx1_inv : InvS (x1.regs iReg) x1 := by
    refine ⟨by wram_simp [x1, x0]; exact Nat.zero_le _, ?_, ?_, ?_, rfl, ?_⟩
    · wram_simp [x1, x0, hx_n]
    · wram_simp [x1, x0, hx_1]
    · wram_simp [x1, x0, hx_cur]
    · wram_simp [x1, x0]; exact (Finset.sum_eq_zero fun _ _ => by simp).symm
  have hx1_le : x1.regs iReg ≤ I.n := by wram_simp [x1, x0]; exact Nat.zero_le _
  obtain ⟨y, hy, hy_inv, _⟩ := ExecWithin.loop_count (w := w) (T := 4)
    (body := ram[
      addr1 ← curBase + iReg;
      tmpReg ← *addr1;
      accReg ← accReg + tmpReg;
      iReg ← iReg + oneReg ]) InvS (fun _ h => h.2.1)
    (fun d hd hlt => by
      obtain ⟨hi_le, dn, d1, dcur, dm, dacc⟩ := hd
      have hi_lt : d.regs iReg < I.n := hlt
      let u0 : Fin I.n := ⟨d.regs iReg, hi_lt⟩
      have hf_addr : Fits w (d.regs curBase + d.regs iReg) :=
        haddr_bound.of_le (by rw [dcur]; omega)
      have hread : d.mem (2 + I.n * I.n + I.n + u0.1) =
          walkCountFrom I.adj (maskSet I.n k) (I.n - 1) u0 := by rw [dm]; exact hmem_cur u0
      have hf_val : Fits w (d.mem (d.regs curBase + d.regs iReg)) := by
        rw [dcur]; change Fits w (d.mem (2 + I.n * I.n + I.n + u0.1)); rw [hread]
        exact hval_fit.of_le ((walkCountFrom_le_pow I.adj _ (I.n - 1) u0).trans
          ((Nat.pow_le_pow_left (Nat.le_succ _) _).trans
            (Nat.pow_le_pow_right (by omega) (by omega))))
      have hsplit : ∑ u : Fin I.n, (if u.1 < u0.1 + 1 then
          walkCountFrom I.adj (maskSet I.n k) (I.n - 1) u else 0) =
          (∑ u : Fin I.n, if u.1 < u0.1 then
            walkCountFrom I.adj (maskSet I.n k) (I.n - 1) u else 0) +
          walkCountFrom I.adj (maskSet I.n k) (I.n - 1) u0 := by
        have heq : ∑ u : Fin I.n, (if u = u0 then
            walkCountFrom I.adj (maskSet I.n k) (I.n - 1) u0 else 0) =
            walkCountFrom I.adj (maskSet I.n k) (I.n - 1) u0 := by simp
        rw [← heq, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun u _ => ?_
        by_cases hu : u = u0
        · subst hu; simp
        · have hne : u.1 ≠ u0.1 := fun h => hu (Fin.ext h)
          simp [hu, show u.1 < u0.1 + 1 ↔ u.1 < u0.1 by omega]
      have hread' : d.mem (2 + I.n * I.n + I.n + d.regs iReg) =
          walkCountFrom I.adj (maskSet I.n k) (I.n - 1) u0 := hread
      have hsplit' : ∑ u : Fin I.n, (if u.1 < d.regs iReg + 1 then
          walkCountFrom I.adj (maskSet I.n k) (I.n - 1) u else 0) =
          (∑ u : Fin I.n, if u.1 < d.regs iReg then
            walkCountFrom I.adj (maskSet I.n k) (I.n - 1) u else 0) +
          walkCountFrom I.adj (maskSet I.n k) (I.n - 1) u0 := hsplit
      have hf_acc : Fits w (d.regs accReg + d.mem (d.regs curBase + d.regs iReg)) := by
        rw [dcur, hread', dacc, ← hsplit']
        have hle_tot : ∑ u : Fin I.n, (if u.1 < d.regs iReg + 1 then
            walkCountFrom I.adj (maskSet I.n k) (I.n - 1) u else 0) ≤
            totalWalkCount I.adj (maskSet I.n k) := by
          rw [totalWalkCount_eq_sum hn]
          refine Finset.sum_le_sum fun u _ => ?_
          split_ifs <;> omega
        exact hval_fit.of_le (hle_tot.trans (totalWalkCount_le I.adj _))
      have hf_i : Fits w (d.regs iReg + d.regs oneReg) := by
        rw [d1]; exact hn_fit.of_le (by omega)
      let z : Data 22 :=
        (((d.set addr1 (2 + I.n * I.n + I.n + d.regs iReg)).set tmpReg
          (walkCountFrom I.adj (maskSet I.n k) (I.n - 1) u0)).set accReg
          (∑ u : Fin I.n, if u.1 < d.regs iReg + 1 then
            walkCountFrom I.adj (maskSet I.n k) (I.n - 1) u else 0)).set iReg
          (d.regs iReg + 1)
      have hz_ex : ExecWithin w (ram[
          addr1 ← curBase + iReg;
          tmpReg ← *addr1;
          accReg ← accReg + tmpReg;
          iReg ← iReg + oneReg ]) d z 4 := by
        wram_exec [dcur, hread', dacc, hsplit', d1]
        · rw [← hsplit']
        · rw [← dacc, ← hread']
          rw [dcur] at hf_acc
          exact hf_acc
      refine ⟨z, hz_ex, ⟨by omega, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · wram_simp [z, dn]
      · wram_simp [z, d1]
      · wram_simp [z, dcur]
      · wram_simp [z, dm]
      · wram_simp [z]
      · wram_simp [z])
    hx1_le hx1_inv
  have hy_time : ExecWithin w (Code.loop (.lt iReg nReg) ram[
      addr1 ← curBase + iReg; tmpReg ← *addr1; accReg ← accReg + tmpReg;
      iReg ← iReg + oneReg ]) x1 y (6 * I.n + 2) := by
    refine hy.mono ?_
    have hx1_0 : x1.regs iReg = 0 := by wram_simp [x1, x0]
    rw [hx1_0, Nat.sub_zero]; ring_nf; exact le_rfl
  refine ⟨y, (hx0_ex.seq (hx1_ex.seq hy_time)).mono (by omega), hy_inv.2.2.2.2.1, ?_,
    fun reg hreg => ?_⟩
  · rw [hy_inv.2.2.2.2.2, totalWalkCount_eq_sum hn]
    refine Finset.sum_congr rfl fun u _ => ?_
    simp [u.isLt]
  · have hloop_pres : (Code.loop (.lt iReg nReg) ram[
        addr1 ← curBase + iReg; tmpReg ← *addr1; accReg ← accReg + tmpReg;
        iReg ← iReg + oneReg ]).Preserves reg := by
      simp only [Code.Preserves, Op.dest, Op.bin, ne_eq, Option.some.injEq]
      exact ⟨hreg.2.2.1.symm, hreg.2.2.2.symm, hreg.2.1.symm, hreg.1.symm⟩
    rw [hy.regs_eq hloop_pres]
    wram_simp [x1, x0, hreg.1, hreg.2.1]

private theorem testBit_succ_eq (k u : ℕ) :
    (k + 1).testBit u =
      if ∀ j < u, k.testBit j = true then !(k.testBit u) else k.testBit u := by
  induction u generalizing k with
  | zero =>
    simp only [Nat.testBit_zero]
    by_cases he : k % 2 = 0
    · simp [Nat.add_mod, he]
    · have h1 : k % 2 = 1 := by omega
      simp [Nat.add_mod, h1]
  | succ u ih =>
    rw [Nat.testBit_succ, Nat.testBit_succ]
    by_cases h0 : k % 2 = 0
    · have hdiv : (k + 1) / 2 = k / 2 := by omega
      have hf : ¬ ∀ j < u + 1, k.testBit j = true := by
        intro h
        have hzero := h 0 (Nat.succ_pos _)
        simp [Nat.testBit_zero, h0] at hzero
      rw [hdiv, ite_eq_right hf]
    · have h1 : k % 2 = 1 := by omega
      have hdiv : (k + 1) / 2 = k / 2 + 1 := by omega
      rw [hdiv, ih (k / 2)]
      have hiff : (∀ j < u, (k / 2).testBit j = true) ↔ ∀ j < u + 1, k.testBit j = true := by
        constructor
        · intro h j hj
          cases j with
          | zero => simp [Nat.testBit_zero, h1]
          | succ j => rw [Nat.testBit_succ]; exact h j (by omega)
        · intro h j hj
          rw [← Nat.testBit_succ]
          exact h (j + 1) (by omega)
      simp only [hiff]

private theorem card_maskSet_succ_prefix_mod {n k t : ℕ}
    (h1 : ∀ j < t, k.testBit j = true)
    (h0 : t = n ∨ (t < n ∧ k.testBit t = false)) :
    (maskSet n (k + 1)).card % 2 =
      ((maskSet n k).card + if t = n then n else t + 1) % 2 := by
  rcases h0 with htn | ⟨htn, h0t⟩
  · subst htn
    have hfull : maskSet t k = Finset.univ := by
      ext u; simp [mem_maskSet, h1 u.1 u.isLt]
    have hempty : maskSet t (k + 1) = ∅ := by
      ext u
      simp only [mem_maskSet, Finset.notMem_empty, iff_false]
      rw [testBit_succ_eq]
      have hall : ∀ j < u.1, k.testBit j = true := fun j hj => h1 j (hj.trans u.isLt)
      rw [ite_eq_left hall]
      simp [h1 u.1 u.isLt]
    rw [hempty, hfull, Finset.card_empty, Finset.card_univ, Fintype.card_fin]
    simp [← two_mul]
  · have hsplit : (maskSet n (k + 1)).card + t = (maskSet n k).card + 1 := by
      let S1 : Finset (Fin n) := Finset.univ.filter fun u : Fin n => u.1 < t
      let tFin : Fin n := ⟨t, htn⟩
      have ht_not : tFin ∉ maskSet n k := by simp [mem_maskSet, h0t, tFin]
      have ht_in : tFin ∈ maskSet n (k + 1) := by
        simp only [mem_maskSet, testBit_succ_eq, tFin]
        rw [ite_eq_left h1, h0t]
        rfl
      have hS1_sub : S1 ⊆ maskSet n k := fun u hu => by
        simp only [S1, Finset.mem_filter, Finset.mem_univ, true_and] at hu
        exact mem_maskSet.2 (h1 u.1 hu)
      have hS1_card : S1.card = t := by
        have hinj : Function.Injective (fun j : Fin t => (⟨j.1, j.isLt.trans htn⟩ : Fin n)) :=
          fun a b h => Fin.ext (by simpa using congrArg Fin.val h)
        have himg : S1 = (Finset.univ : Finset (Fin t)).image
            (fun j : Fin t => (⟨j.1, j.isLt.trans htn⟩ : Fin n)) := by
          ext u
          simp only [S1, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
          exact ⟨fun hu => ⟨⟨u.1, hu⟩, rfl⟩, fun ⟨j, hj⟩ => by subst hj; exact j.isLt⟩
        rw [himg, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
      have hset_eq : maskSet n (k + 1) = insert tFin (maskSet n k \ S1) := by
        ext u
        simp only [Finset.mem_insert, Finset.mem_sdiff, mem_maskSet, S1, Finset.mem_filter,
          Finset.mem_univ, true_and, testBit_succ_eq]
        rcases lt_trichotomy u.1 t with hlt | heq | hgt
        · have hall : ∀ j < u.1, k.testBit j = true := fun j hj => h1 j (hj.trans hlt)
          have hne : u ≠ tFin := fun h => by
            have := congrArg Fin.val h; dsimp [tFin] at this; omega
          rw [ite_eq_left hall]
          simp [h1 u.1 hlt, hne, hlt]
        · have hu_eq : u = tFin := Fin.ext heq
          subst hu_eq
          rw [ite_eq_left h1]
          simp [h0t, tFin]
        · have hnot : ¬ ∀ j < u.1, k.testBit j = true := fun h => by
            have := h t hgt
            rw [h0t] at this
            simp at this
          have hne : u ≠ tFin := fun h => by
            have := congrArg Fin.val h; dsimp [tFin] at this; omega
          rw [ite_eq_right hnot]
          simp [hne, show ¬ u.1 < t by omega]
      have ht_not_diff : tFin ∉ maskSet n k \ S1 := fun h => ht_not (Finset.mem_sdiff.1 h).1
      rw [hset_eq, Finset.card_insert_of_notMem ht_not_diff, Finset.card_sdiff_of_subset hS1_sub,
        hS1_card]
      have hle : t ≤ (maskSet n k).card := hS1_card ▸ Finset.card_le_card hS1_sub
      omega
    have hif : (if t = n then n else t + 1) = t + 1 := ite_eq_right htn.ne
    rw [hif]
    have h2 : (maskSet n (k + 1)).card + 2 * t = (maskSet n k).card + (t + 1) := by omega
    rw [← h2, Nat.add_mul_mod_self_left]

private theorem exec_odometerCode {w : ℕ} (I : Instance) (k : ℕ) (hfit : I.FitsWidth w)
    (x : Data 22)
    (hx_n : x.regs nReg = I.n) (hx_1 : x.regs oneReg = 1)
    (hx_in : x.regs inBase = 2 + I.n * I.n)
    (hx_mp : x.regs maskParity = (maskSet I.n k).card % 2)
    (hmem_in : ∀ u : Fin I.n, x.mem (2 + I.n * I.n + u.1) = if k.testBit u.1 then 1 else 0) :
    ∃ y, ExecWithin w odometerCode x y (10 * I.n + 3) ∧
      y.regs maskParity = (maskSet I.n (k + 1)).card % 2 ∧
      (∀ u : Fin I.n, y.mem (2 + I.n * I.n + u.1) = if (k + 1).testBit u.1 then 1 else 0) ∧
      (∀ a, ¬ (2 + I.n * I.n ≤ a ∧ a < 2 + I.n * I.n + I.n) → y.mem a = x.mem a) ∧
      (∀ reg : Fin 22, reg ≠ iReg ∧ reg ≠ accReg ∧ reg ≠ addr1 ∧ reg ≠ tmpReg ∧
        reg ≠ maskParity → y.regs reg = x.regs reg) := by
  have h1_le := one_le_word_prod I.n
  have hn_fit : Fits w I.n := hfit.of_le (by unfold Instance.wordBound; nlinarith)
  have h0_fit : Fits w 0 := hfit.of_le (by unfold Instance.wordBound; omega)
  have h1_fit : Fits w 1 := hfit.of_le (by unfold Instance.wordBound; omega)
  have haddr_bound : Fits w (2 + I.n * I.n + 3 * I.n) :=
    hfit.of_le (by unfold Instance.wordBound; nlinarith)
  unfold odometerCode
  let x1 : Data 22 := x.set iReg 0
  have hx1_ex : ExecWithin w (.op (.const iReg 0)) x x1 1 :=
    ExecWithin.const (B := .standard) h0_fit
  let InvO (d : Data 22) : Prop :=
    d.regs iReg ≤ I.n ∧ d.regs nReg = I.n ∧ d.regs oneReg = 1 ∧ d.regs inBase = 2 + I.n * I.n ∧
    (∃ t ≤ I.n, (∀ j < t, k.testBit j = true) ∧
      ((d.regs iReg = t ∧ d.regs maskParity = ((maskSet I.n k).card + t) % 2 ∧
        (∀ u : Fin I.n, d.mem (2 + I.n * I.n + u.1) =
          if u.1 < t then 0 else if k.testBit u.1 then 1 else 0)) ∨
      (d.regs iReg = I.n ∧ t < I.n ∧ k.testBit t = false ∧
        d.regs maskParity = (maskSet I.n (k + 1)).card % 2 ∧
        (∀ u : Fin I.n, d.mem (2 + I.n * I.n + u.1) =
          if (k + 1).testBit u.1 then 1 else 0)))) ∧
    (∀ a, ¬ (2 + I.n * I.n ≤ a ∧ a < 2 + I.n * I.n + I.n) → d.mem a = x.mem a)
  have hx1_inv : InvO x1 := by
    refine ⟨Nat.zero_le _, ?_, ?_, ?_, ⟨0, Nat.zero_le _, fun _ hj => by omega,
      Or.inl ⟨?_, ?_, ?_⟩⟩, fun _ _ => rfl⟩
    · wram_simp [x1, hx_n]
    · wram_simp [x1, hx_1]
    · wram_simp [x1, hx_in]
    · wram_simp [x1]
    · wram_simp [x1, hx_mp]
    · intro u; wram_simp [x1, hmem_in u]
  obtain ⟨y, hy, hy_inv, hy_stop⟩ := ExecWithin.loop_invariant
    (w := w) (cond := .lt iReg nReg)
    (body := ram[
      addr1 ← inBase + iReg;
      accReg ← *addr1;
      if accReg = oneReg then [
        tmpReg ← #0;
        *addr1 ← tmpReg;
        maskParity ← oneReg - maskParity;
        iReg ← iReg + oneReg
      ] else [
        *addr1 ← oneReg;
        maskParity ← oneReg - maskParity;
        iReg ← nReg
      ] ]) InvO (fun d => I.n - d.regs iReg) (T := 8)
    (fun d hd hcond => by
      obtain ⟨hi_le, dn, d1, din, ⟨t, ht_le, h1t, ht_disj⟩, d_out⟩ := hd
      have hi_lt : d.regs iReg < I.n := by
        have hlt' : d.regs iReg < d.regs nReg := by simpa only [Cond.holds_lt] using hcond
        rwa [dn] at hlt'
      rcases ht_disj with ⟨hit, hmp, hdmem⟩ | ⟨hit_n, _⟩
      · have ht_lt : t < I.n := hit ▸ hi_lt
        let tFin : Fin I.n := ⟨t, ht_lt⟩
        have hf_addr : Fits w (d.regs inBase + d.regs iReg) :=
          haddr_bound.of_le (by rw [din, hit]; omega)
        have hread : d.mem (2 + I.n * I.n + t) = if k.testBit t then 1 else 0 := by
          simpa [tFin] using hdmem tFin
        have hf_acc_fit : Fits w (d.mem (d.regs inBase + d.regs iReg)) := by
          rw [din, hit, hread]
          split_ifs <;> exact h1_fit.of_le (by decide)
        have hmp_lt2 : d.regs maskParity < 2 := by rw [hmp]; exact Nat.mod_lt _ (by decide)
        have hf_sub : Fits w (d.regs oneReg - d.regs maskParity) := by
          rw [d1]; exact h1_fit.of_le (by omega)
        have hf_t1 : Fits w (d.regs iReg + d.regs oneReg) := by
          rw [d1, hit]; exact hn_fit.of_le (by omega)
        by_cases hbit : k.testBit t = true
        · refine (WP.seq ?_).exists_execWithin
          wram_exec [din, hit, hread, d1, hbit]
          refine ⟨⟨?_, ?_, ?_, ?_, ⟨t + 1, by omega, fun j hj => ?_,
            Or.inl ⟨?_, ?_, fun u => ?_⟩⟩, ?_⟩, ?_⟩
          · wram_simp [hit, d1]; omega
          · wram_simp [dn]
          · wram_simp [d1]
          · wram_simp [din]
          · rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.1 hj) with hlt' | rfl
            · exact h1t j hlt'
            · exact hbit
          · wram_simp [hit, d1]
          · wram_simp [d1, hmp]; omega
          · by_cases hut : u.1 = t
            · subst hut
              wram_simp [Data.write, din, hit, Function.update_self]
              simp
            · have hne : 2 + I.n * I.n + u.1 ≠ 2 + I.n * I.n + t := by omega
              wram_simp [Data.write, din, hit, Function.update_of_ne hne, hdmem u]
              have hiff : u.1 < t + 1 ↔ u.1 < t := by omega
              simp [hiff]
          · intro a ha
            have hne : a ≠ 2 + I.n * I.n + t := by omega
            wram_simp [Data.write, din, hit, Function.update_of_ne hne, d_out a ha]
          · wram_simp [hit, d1]; omega
        · have hbit_f : k.testBit t = false := by cases hm : k.testBit t <;> simp_all
          have hcard_next := card_maskSet_succ_prefix_mod h1t (Or.inr ⟨ht_lt, hbit_f⟩)
          rw [ite_eq_right ht_lt.ne] at hcard_next
          refine (WP.seq ?_).exists_execWithin
          wram_exec [din, hit, hread, d1, hbit_f, dn]
          refine ⟨⟨?_, ?_, ?_, ?_, ⟨t, ht_lt.le, h1t,
            Or.inr ⟨?_, ht_lt, hbit_f, ?_, fun u => ?_⟩⟩, ?_⟩, ?_⟩
          · wram_simp [dn]; exact le_rfl
          · wram_simp [dn]
          · wram_simp [d1]
          · wram_simp [din]
          · wram_simp [dn]
          · wram_simp [d1, hmp, hcard_next]; omega
          · by_cases hut : u.1 = t
            · subst hut
              wram_simp [Data.write, din, hit, d1, Function.update_self, testBit_succ_eq, hbit_f]
              rw [ite_eq_left h1t]
              simp
            · have hne : 2 + I.n * I.n + u.1 ≠ 2 + I.n * I.n + t := by omega
              wram_simp [Data.write, din, hit, Function.update_of_ne hne, hdmem u]
              rw [testBit_succ_eq]
              rcases lt_trichotomy u.1 t with hlt' | heq' | hgt'
              · have hall : ∀ j < u.1, k.testBit j = true := fun j hj => h1t j (hj.trans hlt')
                rw [ite_eq_left hall]
                simp [hlt', h1t u.1 hlt']
              · exact absurd heq' hut
              · have hnot : ¬ ∀ j < u.1, k.testBit j = true := fun h => by
                  have := h t hgt'
                  rw [hbit_f] at this
                  simp at this
                rw [ite_eq_right hnot]
                simp [show ¬ u.1 < t by omega]
          · intro a ha
            have hne : a ≠ 2 + I.n * I.n + t := by omega
            wram_simp [Data.write, din, hit, Function.update_of_ne hne, d_out a ha]
          · wram_simp [hit, dn]; omega
      · omega) hx1_inv
  have hy_i : y.regs iReg = I.n := by
    obtain ⟨hi_le, dn, -⟩ := hy_inv
    have hnot : ¬ y.regs iReg < y.regs nReg := by simpa only [Cond.holds_lt] using hy_stop
    rw [dn] at hnot
    omega
  obtain ⟨_, _, _, _, ⟨t, ht_le, h1t, ht_disj⟩, hy_out⟩ := hy_inv
  refine ⟨y, (hx1_ex.seq (hy.mono (by
      have hx1_0 : x1.regs iReg = 0 := by wram_simp [x1]
      rw [hx1_0, Nat.sub_zero]))).mono (by omega), ?_, ?_, hy_out, fun reg hreg => ?_⟩
  · rcases ht_disj with ⟨hit, hmp, _⟩ | ⟨_, _, _, hmp, _⟩
    · have rfl_t : t = I.n := hit.symm.trans hy_i
      subst rfl_t
      have hc := card_maskSet_succ_prefix_mod h1t (Or.inl rfl)
      simp only [↓reduceIte] at hc
      rw [hmp, ← hc]
    · exact hmp
  · rcases ht_disj with ⟨hit, _, hymem⟩ | ⟨_, _, _, _, hymem⟩
    · have rfl_t : t = I.n := hit.symm.trans hy_i
      subst rfl_t
      intro u
      rw [hymem u, ite_eq_left u.isLt, testBit_succ_eq]
      have hall : ∀ j < u.1, k.testBit j = true := fun j hj => h1t j (hj.trans u.isLt)
      rw [ite_eq_left hall]
      simp [h1t u.1 u.isLt]
    · exact hymem
  · have hloop_pres : (Code.loop (.lt iReg nReg) ram[
        addr1 ← inBase + iReg;
        accReg ← *addr1;
        if accReg = oneReg then [
          tmpReg ← #0;
          *addr1 ← tmpReg;
          maskParity ← oneReg - maskParity;
          iReg ← iReg + oneReg
        ] else [
          *addr1 ← oneReg;
          maskParity ← oneReg - maskParity;
          iReg ← nReg
        ] ]).Preserves reg := by
      simp only [Code.Preserves, Op.dest, Op.bin, ne_eq, Option.some.injEq]
      exact ⟨hreg.2.2.1.symm, hreg.2.1.symm,
        ⟨hreg.2.2.2.1.symm, by simp, hreg.2.2.2.2.symm, hreg.1.symm⟩,
        ⟨by simp, hreg.2.2.2.2.symm, hreg.1.symm⟩⟩
    rw [hy.regs_eq hloop_pres]
    wram_simp [x1, hreg.1]

/-! ## Mask iteration, main program, and `O((n³ + 1) · 2 ^ n)` bounds -/

private noncomputable def evenPart (I : Instance) (m : ℕ) : ℕ :=
  ∑ j ∈ Finset.range m,
    if (maskSet I.n j).card % 2 = I.n % 2 then totalWalkCount I.adj (maskSet I.n j) else 0

private noncomputable def oddPart (I : Instance) (m : ℕ) : ℕ :=
  ∑ j ∈ Finset.range m,
    if (maskSet I.n j).card % 2 ≠ I.n % 2 then totalWalkCount I.adj (maskSet I.n j) else 0

private theorem evenPart_succ (I : Instance) (k : ℕ) :
    evenPart I (k + 1) = evenPart I k +
      if (maskSet I.n k).card % 2 = I.n % 2 then totalWalkCount I.adj (maskSet I.n k) else 0 :=
  Finset.sum_range_succ _ k

private theorem oddPart_succ (I : Instance) (k : ℕ) :
    oddPart I (k + 1) = oddPart I k +
      if (maskSet I.n k).card % 2 ≠ I.n % 2 then totalWalkCount I.adj (maskSet I.n k) else 0 :=
  Finset.sum_range_succ _ k

private theorem part_le_mul (I : Instance) {m : ℕ} (hm : m ≤ 2 ^ I.n) :
    evenPart I m ≤ 2 ^ I.n * (I.n + 1) ^ I.n ∧ oddPart I m ≤ 2 ^ I.n * (I.n + 1) ^ I.n := by
  have hbound : ∀ (p : ℕ → Prop) [DecidablePred p],
      ∑ j ∈ Finset.range m, (if p j then totalWalkCount I.adj (maskSet I.n j) else 0) ≤
        2 ^ I.n * (I.n + 1) ^ I.n := fun p _ => by
    calc ∑ j ∈ Finset.range m, (if p j then totalWalkCount I.adj (maskSet I.n j) else 0)
        ≤ ∑ _j ∈ Finset.range m, (I.n + 1) ^ I.n := by
          refine Finset.sum_le_sum fun j _ => ?_
          split_ifs
          · exact totalWalkCount_le I.adj _
          · exact Nat.zero_le _
      _ = m * (I.n + 1) ^ I.n := by simp
      _ ≤ 2 ^ I.n * (I.n + 1) ^ I.n := Nat.mul_le_mul_right _ hm
  exact ⟨hbound _, hbound _⟩

private theorem evenPart_sub_oddPart (I : Instance) :
    (evenPart I (2 ^ I.n) : ℤ) - (oddPart I (2 ^ I.n) : ℤ) = #(hamPaths I.adj) := by
  have hcast : ∀ (m : ℕ), (evenPart I m : ℤ) - (oddPart I m : ℤ) =
      ∑ j ∈ Finset.range m,
        (-1 : ℤ) ^ (I.n - (maskSet I.n j).card) * (totalWalkCount I.adj (maskSet I.n j) : ℤ) := by
    intro m
    induction m with
    | zero => simp [evenPart, oddPart]
    | succ m ih =>
      rw [evenPart_succ, oddPart_succ, Finset.sum_range_succ]
      push_cast
      have hcard_le : (maskSet I.n m).card ≤ I.n := by
        simpa [Fintype.card_fin] using Finset.card_le_univ (maskSet I.n m)
      have hpar : ((-1 : ℤ) ^ (I.n - (maskSet I.n m).card)) =
          if (maskSet I.n m).card % 2 = I.n % 2 then 1 else -1 := by
        have hdiff : Even (I.n - (maskSet I.n m).card) ↔ (maskSet I.n m).card % 2 = I.n % 2 := by
          rw [Nat.even_iff]
          omega
        by_cases hp : (maskSet I.n m).card % 2 = I.n % 2
        · simp [hp, (hdiff.2 hp).neg_one_pow]
        · have hodd : Odd (I.n - (maskSet I.n m).card) := by
            rw [Nat.odd_iff]
            have : ¬ Even (I.n - (maskSet I.n m).card) := fun h => hp (hdiff.1 h)
            rw [Nat.even_iff] at this
            omega
          simp [hp, hodd.neg_one_pow]
      by_cases hp : (maskSet I.n m).card % 2 = I.n % 2
      · simp only [hp, ↓reduceIte, ne_eq, not_true_eq_false] at hpar ⊢
        rw [hpar, one_mul]
        omega
      · simp only [hp, ↓reduceIte, ne_eq, not_false_eq_true] at hpar ⊢
        rw [hpar]
        omega
  rw [hcast, ← countHamPaths_eq I.adj, countHamPaths]
  have hsum_fin : (Fin.foldl (2 ^ I.n) (fun (acc : ℤ) (k : Fin (2 ^ I.n)) =>
      acc + (-1 : ℤ) ^ (I.n - maskCard I.n k) * (subsetWalks I.adj k : ℤ)) 0) =
      ∑ k : Fin (2 ^ I.n),
        (-1 : ℤ) ^ (I.n - (maskSet I.n k.1).card) *
          (totalWalkCount I.adj (maskSet I.n k.1) : ℤ) := by
    have hfold : ∀ (m : ℕ) (f : Fin m → ℤ),
        Fin.foldl m (fun acc i => acc + f i) 0 = ∑ i : Fin m, f i := by
      intro m f
      induction m with
      | zero => simp
      | succ m ih => rw [Fin.foldl_succ_last, ih, Fin.sum_univ_castSucc]
    rw [hfold]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [maskCard_eq_card_maskSet, subsetWalks_eq]
  rw [hsum_fin, Finset.sum_range]

private theorem branchPos_time_le {n : ℕ} (hn : 0 < n) :
    (7 * n + 3) + ((n - 1) * (n * (10 * n + 15) + 7 * n + 9) + 3 + (6 * n + 4)) + 1 ≤
      if n = 0 then 3 else 10 * n ^ 3 + 12 * n ^ 2 + 13 * n + 12 := by
  rw [ite_eq_right hn.ne']
  have hsub : n = (n - 1) + 1 := by omega
  generalize hm : n - 1 = m
  rw [hm] at hsub
  rw [hsub]
  nlinarith

private theorem maskBody_time_le (n : ℕ) :
    1 + ((if n = 0 then 3 else 10 * n ^ 3 + 12 * n ^ 2 + 13 * n + 12) +
      (3 + ((10 * n + 3) + 1))) ≤ if n = 0 then 16 else 36 * (n ^ 3 + 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn_pos
  · simp
  · rw [ite_eq_right hn_pos.ne', ite_eq_right hn_pos.ne']
    have hsub : n = (n - 1) + 1 := by omega
    generalize hm : n - 1 = m
    rw [hm] at hsub
    rw [hsub]
    have hc : 1 ≤ (m + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    have hc3 : m + 1 ≤ (m + 1) ^ 3 := by nlinarith
    nlinarith

private theorem exec_maskBodyCode {w : ℕ} (I : Instance) (k : ℕ) (hfit : I.FitsWidth w)
    (hk : k < 2 ^ I.n) (x : Data 22)
    (hx_n : x.regs nReg = I.n) (hx_nm1 : x.regs nMinus1 = I.n - 1)
    (hx_1 : x.regs oneReg = 1) (hx_adj : x.regs adjBase = 2)
    (hx_in : x.regs inBase = 2 + I.n * I.n)
    (hx_cur : x.regs curBase = 2 + I.n * I.n + I.n)
    (hx_next : x.regs nextBase = 2 + I.n * I.n + 2 * I.n)
    (hx_k : x.regs kReg = k) (hx_np : x.regs nParity = I.n % 2)
    (hx_mp : x.regs maskParity = (maskSet I.n k).card % 2)
    (hx_ev : x.regs evenSum = evenPart I k) (hx_od : x.regs oddSum = oddPart I k)
    (hmem_adj : memAddrOK I x.mem)
    (hmem_in : ∀ u : Fin I.n, x.mem (2 + I.n * I.n + u.1) = if k.testBit u.1 then 1 else 0) :
    ∃ y, ExecWithin w maskBodyCode x y (if I.n = 0 then 16 else 36 * (I.n ^ 3 + 1)) ∧
      y.regs nReg = I.n ∧ y.regs nMinus1 = I.n - 1 ∧
      y.regs oneReg = 1 ∧ y.regs adjBase = 2 ∧
      y.regs inBase = 2 + I.n * I.n ∧
      y.regs curBase = 2 + I.n * I.n + I.n ∧
      y.regs nextBase = 2 + I.n * I.n + 2 * I.n ∧
      y.regs kReg = k + 1 ∧ y.regs nParity = I.n % 2 ∧
      y.regs maskParity = (maskSet I.n (k + 1)).card % 2 ∧
      y.regs evenSum = evenPart I (k + 1) ∧ y.regs oddSum = oddPart I (k + 1) ∧
      memAddrOK I y.mem ∧
      (∀ u : Fin I.n, y.mem (2 + I.n * I.n + u.1) = if (k + 1).testBit u.1 then 1 else 0) := by
  have h1_le := one_le_word_prod I.n
  have h0_fit : Fits w 0 := hfit.of_le (by unfold Instance.wordBound; omega)
  have h1_fit : Fits w 1 := hfit.of_le (by unfold Instance.wordBound; omega)
  have haddr_bound : Fits w (2 + I.n * I.n + 3 * I.n) :=
    hfit.of_le (by unfold Instance.wordBound; nlinarith)
  have hk1_fit : Fits w (k + 1) :=
    hfit.of_le (by
      have hpow_le : 2 ^ I.n ≤ 2 ^ I.n * (I.n + 1) ^ I.n :=
        Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ (by omega))
      unfold Instance.wordBound; omega)
  have hev_fit : Fits w (evenPart I (k + 1)) :=
    hfit.of_le (by
      have hle : k + 1 ≤ 2 ^ I.n := by omega
      have := (part_le_mul I hle).1
      unfold Instance.wordBound; omega)
  have hod_fit : Fits w (oddPart I (k + 1)) :=
    hfit.of_le (by
      have hle : k + 1 ≤ 2 ^ I.n := by omega
      have := (part_le_mul I hle).2
      unfold Instance.wordBound; omega)
  let s0 : Data 22 := x.set tmpReg 0
  have hs0_ex : ExecWithin w (.op (.const tmpReg 0)) x s0 1 :=
    ExecWithin.const (B := .standard) h0_fit
  have hbranch_pos : ∃ s1, ExecWithin w (ram[
      if tmpReg < nReg then [
        ⟪copyVec inBase curBase⟫;
        ⟪roundsCode⟫;
        ⟪sumVecCode⟫
      ] else [
        accReg ← #1
      ]]) s0 s1 (if I.n = 0 then 3 else 10 * I.n ^ 3 + 12 * I.n ^ 2 + 13 * I.n + 12) ∧
      s1.regs accReg = totalWalkCount I.adj (maskSet I.n k) ∧
      memAddrOK I s1.mem ∧
      (∀ u : Fin I.n, s1.mem (2 + I.n * I.n + u.1) = if k.testBit u.1 then 1 else 0) ∧
      (∀ reg : Fin 22, reg ∈ [nReg, nMinus1, oneReg, adjBase, inBase, curBase, nextBase,
        kReg, nParity, maskParity, evenSum, oddSum] → s1.regs reg = x.regs reg) := by
    by_cases hn_pos : 0 < I.n
    · have hs0_n : s0.regs nReg = I.n := by wram_simp [s0, hx_n]
      have hs0_0 : s0.regs tmpReg = 0 := by wram_simp [s0]
      have hcond : Cond.Holds (.lt tmpReg nReg) s0 := by
        change s0.regs tmpReg < s0.regs nReg
        rw [hs0_0, hs0_n]
        exact hn_pos
      have hv_fit : vecFits I w (2 + I.n * I.n) s0.mem := fun u => by
        wram_simp [s0, hmem_in u]
        split_ifs <;> exact h1_fit.of_le (by decide)
      obtain ⟨s1, hs1, s1_cur, s1_out, s1_regs⟩ := exec_copyVec I inBase curBase
        (2 + I.n * I.n) (2 + I.n * I.n + I.n) (by decide) (by decide) (fun u v => by omega)
        hfit ⟨haddr_bound.of_le (by omega), haddr_bound.of_le (by omega)⟩ s0
        hs0_n (by wram_simp [s0, hx_1]) (by wram_simp [s0, hx_in])
        (by wram_simp [s0, hx_cur]) hv_fit
      have s1_adj : memAddrOK I s1.mem := fun u v => by
        rw [s1_out _ (by have := adj_index_lt u v; omega)]
        wram_simp [s0]
        exact hmem_adj u v
      have s1_in : ∀ u : Fin I.n, s1.mem (2 + I.n * I.n + u.1) = if k.testBit u.1 then 1 else 0 :=
        fun u => by rw [s1_out _ (by omega)]; wram_simp [s0]; exact hmem_in u
      have s1_cur0 : ∀ u : Fin I.n,
          s1.mem (2 + I.n * I.n + I.n + u.1) =
            walkCountFrom I.adj (maskSet I.n k) 0 u := fun u => by
        rw [s1_cur u]; wram_simp [s0, hmem_in u, walkCountFrom, mem_maskSet]
      obtain ⟨s2, hs2, s2_cur, s2_out, s2_regs⟩ := exec_roundsCode I k hfit hn_pos s1
        ((s1_regs nReg (by decide)).trans hs0_n)
        ((s1_regs nMinus1 (by decide)).trans (by wram_simp [s0, hx_nm1]))
        ((s1_regs oneReg (by decide)).trans (by wram_simp [s0, hx_1]))
        ((s1_regs adjBase (by decide)).trans (by wram_simp [s0, hx_adj]))
        ((s1_regs inBase (by decide)).trans (by wram_simp [s0, hx_in]))
        ((s1_regs curBase (by decide)).trans (by wram_simp [s0, hx_cur]))
        ((s1_regs nextBase (by decide)).trans (by wram_simp [s0, hx_next]))
        s1_adj s1_in s1_cur0
      obtain ⟨s3, hs3, s3_m, s3_acc, s3_regs⟩ := exec_sumVecCode I k hfit hn_pos s2
        ((s2_regs nReg (by decide)).trans ((s1_regs nReg (by decide)).trans hs0_n))
        ((s2_regs oneReg (by decide)).trans ((s1_regs oneReg (by decide)).trans
          (by wram_simp [s0, hx_1])))
        ((s2_regs curBase (by decide)).trans ((s1_regs curBase (by decide)).trans
          (by wram_simp [s0, hx_cur]))) s2_cur
      refine ⟨s3, (ExecWithin.branch_pos hcond (hs1.seq (hs2.seq hs3))).mono
          (branchPos_time_le hn_pos),
        s3_acc, fun u v => ?_, fun u => ?_, fun reg hmem => ?_⟩
      · rw [s3_m, s2_out _ (by have := adj_index_lt u v; omega)]
        exact s1_adj u v
      · rw [s3_m, s2_out _ (by omega)]
        exact s1_in u
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        · rw [s3_regs _ (by decide), s2_regs _ (by decide), s1_regs _ (by decide)]
          wram_simp [s0, hx_n, hx_nm1, hx_1, hx_adj, hx_in, hx_cur, hx_next,
            hx_k, hx_np, hx_mp, hx_ev, hx_od]
    · have hn0 : I.n = 0 := by omega
      have hneg : ¬ Cond.Holds (.lt tmpReg nReg) s0 := by
        change ¬ (s0.regs tmpReg < s0.regs nReg)
        rw [show s0.regs tmpReg = 0 by wram_simp [s0],
          show s0.regs nReg = 0 by wram_simp [s0, hx_n, hn0]]
        omega
      let s1 : Data 22 := s0.set accReg 1
      have hbr : ExecWithin w (.op (.const accReg 1)) s0 s1 1 :=
        ExecWithin.const (B := .standard) h1_fit
      refine ⟨s1, (ExecWithin.branch_neg hneg hbr).mono (by rw [ite_eq_left hn0]), ?_,
        fun u => Fin.elim0 (hn0 ▸ u), fun u => Fin.elim0 (hn0 ▸ u), fun reg hmem => ?_⟩
      · rw [totalWalkCount_zero hn0]; wram_simp [s1, s0]
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          wram_simp [s1, s0]
  obtain ⟨s1, hs1, s1_acc, s1_adj, s1_in, s1_regs⟩ := hbranch_pos
  have s1_n := s1_regs nReg (by simp)
  have s1_nm1 := s1_regs nMinus1 (by simp)
  have s1_1 := s1_regs oneReg (by simp)
  have s1_adjb := s1_regs adjBase (by simp)
  have s1_inb := s1_regs inBase (by simp)
  have s1_curb := s1_regs curBase (by simp)
  have s1_nextb := s1_regs nextBase (by simp)
  have s1_k := s1_regs kReg (by simp)
  have s1_np := s1_regs nParity (by simp)
  have s1_mp := s1_regs maskParity (by simp)
  have s1_ev := s1_regs evenSum (by simp)
  have s1_od := s1_regs oddSum (by simp)
  have hs2_step : ∃ s2, ExecWithin w (ram[
      if maskParity = nParity then [
        evenSum ← evenSum + accReg
      ] else [
        oddSum ← oddSum + accReg
      ]]) s1 s2 3 ∧
      s2.mem = s1.mem ∧ s2.regs evenSum = evenPart I (k + 1) ∧
      s2.regs oddSum = oddPart I (k + 1) ∧
      (∀ reg : Fin 22, reg ≠ evenSum ∧ reg ≠ oddSum → s2.regs reg = s1.regs reg) := by
    by_cases hpar : (maskSet I.n k).card % 2 = I.n % 2
    · have hcond : Cond.Holds (.eq maskParity nParity) s1 := by
        change s1.regs maskParity = s1.regs nParity
        rw [s1_mp, s1_np, hx_mp, hx_np]
        exact hpar
      have hs_ev_fit : Fits w (s1.regs evenSum + s1.regs accReg) := by
        rw [s1_ev, s1_acc, hx_ev]
        simpa [evenPart_succ, hpar] using hev_fit
      let s2 : Data 22 := s1.set evenSum (evenPart I (k + 1))
      have hs2_br : ExecWithin w (.op (.bin .add evenSum evenSum accReg)) s1 s2 1 := by
        wram_exec [s1_ev, s1_acc, hx_ev]
        simp [s2, evenPart_succ, hpar]
      refine ⟨s2, (ExecWithin.branch_pos hcond hs2_br).mono (by omega), rfl, ?_, ?_,
        fun reg hreg => ?_⟩
      · wram_simp [s2]
      · wram_simp [s2, s1_od, hx_od]; simp [oddPart_succ, hpar]
      · wram_simp [s2, hreg.1]
    · have hcond : ¬ Cond.Holds (.eq maskParity nParity) s1 := by
        change s1.regs maskParity ≠ s1.regs nParity
        rw [s1_mp, s1_np, hx_mp, hx_np]
        exact hpar
      have hs_od_fit : Fits w (s1.regs oddSum + s1.regs accReg) := by
        rw [s1_od, s1_acc, hx_od]
        simpa [oddPart_succ, hpar] using hod_fit
      let s2 : Data 22 := s1.set oddSum (oddPart I (k + 1))
      have hs2_br : ExecWithin w (.op (.bin .add oddSum oddSum accReg)) s1 s2 1 := by
        wram_exec [s1_od, s1_acc, hx_od]
        simp [s2, oddPart_succ, hpar]
      refine ⟨s2, ExecWithin.branch_neg hcond hs2_br, rfl, ?_, ?_, fun reg hreg => ?_⟩
      · wram_simp [s2, s1_ev, hx_ev]; simp [evenPart_succ, hpar]
      · wram_simp [s2]
      · wram_simp [s2, hreg.2]
  obtain ⟨s2, hs2, s2_m, s2_ev, s2_od, s2_regs⟩ := hs2_step
  obtain ⟨s3, hs3, s3_mp, s3_in, s3_out, s3_regs⟩ := exec_odometerCode I k hfit s2
    ((s2_regs nReg (by decide)).trans (s1_n.trans hx_n))
    ((s2_regs oneReg (by decide)).trans (s1_1.trans hx_1))
    ((s2_regs inBase (by decide)).trans (s1_inb.trans hx_in))
    ((s2_regs maskParity (by decide)).trans (s1_mp.trans hx_mp))
    (fun u => by rw [s2_m]; exact s1_in u)
  have hs3_k : s3.regs kReg = k :=
    (s3_regs kReg (by decide)).trans ((s2_regs kReg (by decide)).trans (s1_k.trans hx_k))
  have hs3_1 : s3.regs oneReg = 1 :=
    (s3_regs oneReg (by decide)).trans ((s2_regs oneReg (by decide)).trans (s1_1.trans hx_1))
  have hf_k1 : Fits w (s3.regs kReg + s3.regs oneReg) := by rw [hs3_k, hs3_1]; exact hk1_fit
  have hs4_ex : ∃ s4, ExecWithin w (.op (.bin .add kReg kReg oneReg)) s3 s4 1 ∧
      s4 = s3.set kReg (k + 1) := by
    wram_exec [hs3_k, hs3_1]; rfl
  obtain ⟨s4, hs4, rfl⟩ := hs4_ex
  unfold maskBodyCode
  refine ⟨s3.set kReg (k + 1),
    (hs0_ex.seq (hs1.seq (hs2.seq (hs3.seq hs4)))).mono (maskBody_time_le I.n),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · wram_simp [(s3_regs nReg (by decide)).trans ((s2_regs nReg (by decide)).trans
      (s1_n.trans hx_n))]
  · wram_simp [(s3_regs nMinus1 (by decide)).trans ((s2_regs nMinus1 (by decide)).trans
      (s1_nm1.trans hx_nm1))]
  · wram_simp [hs3_1]
  · wram_simp [(s3_regs adjBase (by decide)).trans ((s2_regs adjBase (by decide)).trans
      (s1_adjb.trans hx_adj))]
  · wram_simp [(s3_regs inBase (by decide)).trans ((s2_regs inBase (by decide)).trans
      (s1_inb.trans hx_in))]
  · wram_simp [(s3_regs curBase (by decide)).trans ((s2_regs curBase (by decide)).trans
      (s1_curb.trans hx_cur))]
  · wram_simp [(s3_regs nextBase (by decide)).trans ((s2_regs nextBase (by decide)).trans
      (s1_nextb.trans hx_next))]
  · wram_simp
  · wram_simp [(s3_regs nParity (by decide)).trans ((s2_regs nParity (by decide)).trans
      (s1_np.trans hx_np))]
  · wram_simp [s3_mp]
  · wram_simp [(s3_regs evenSum (by decide)).trans s2_ev]
  · wram_simp [(s3_regs oddSum (by decide)).trans s2_od]
  · intro u v
    have hm1 : s3.mem (2 + u.1 * I.n + v.1) = s2.mem (2 + u.1 * I.n + v.1) :=
      s3_out _ (by have := adj_index_lt u v; omega)
    wram_simp [Data.set, hm1, s2_m, s1_adj u v]
  · intro u; wram_simp [Data.set, s3_in u]

private theorem maskBodyCode_preserves_maskLimit : maskBodyCode.Preserves maskLimit := by
  have hcopy : (copyVec inBase curBase).Preserves maskLimit := by
    simp only [Code.Preserves, copyVec, Op.dest, ne_eq, Option.some.injEq]
    repeat (first | constructor | decide)
  have hcell : stepCellCode.Preserves maskLimit := by
    simp only [Code.Preserves, stepCellCode, Op.dest, ne_eq, Option.some.injEq]
    repeat (first | constructor | decide)
  have hstep : stepVecCode.Preserves maskLimit := ⟨by decide, hcell⟩
  have hrounds : roundsCode.Preserves maskLimit := by
    simp only [Code.Preserves, roundsCode, Op.dest, ne_eq, Option.some.injEq]
    refine ⟨by decide, hstep, ?_, by decide⟩
    simp only [Code.Preserves, copyVec, Op.dest, ne_eq, Option.some.injEq]
    repeat (first | constructor | decide)
  have hsum : sumVecCode.Preserves maskLimit := by
    simp only [Code.Preserves, sumVecCode, Op.dest, ne_eq, Option.some.injEq]
    repeat (first | constructor | decide)
  have hodo : odometerCode.Preserves maskLimit := by
    simp only [Code.Preserves, odometerCode, Op.dest, ne_eq, Option.some.injEq]
    repeat (first | constructor | decide)
  simp only [Code.Preserves, maskBodyCode, Op.dest, ne_eq, Option.some.injEq]
  exact ⟨by decide, ⟨⟨hcopy, hrounds, hsum⟩, by decide⟩, ⟨by decide, by decide⟩, hodo, by decide⟩

private theorem exec_initRegs {w : ℕ} (I : Instance) (hfit : I.FitsWidth w) :
    ∃ x1, ExecWithin w initRegsCode (Data.init I.encode) x1 15 ∧
      x1.regs nReg = I.n ∧ x1.regs oneReg = 1 ∧ x1.regs twoReg = 2 ∧
      x1.regs adjBase = 2 ∧ x1.regs nMinus1 = I.n - 1 ∧ x1.regs nParity = I.n % 2 ∧
      x1.regs evenSum = 0 ∧ x1.regs oddSum = 0 ∧ x1.regs maskParity = 0 ∧
      x1.regs inBase = 2 + I.n * I.n ∧ x1.regs curBase = 2 + I.n * I.n + I.n ∧
      x1.regs nextBase = 2 + I.n * I.n + 2 * I.n ∧
      x1.regs maskLimit = 1 ∧ x1.regs iReg = 0 ∧
      x1.mem = (Data.init I.encode : Data 22).mem := by
  have h1_le := one_le_word_prod I.n
  have h0_fit : Fits w 0 := hfit.of_le (by unfold Instance.wordBound; omega)
  have h1_fit : Fits w 1 := hfit.of_le (by unfold Instance.wordBound; omega)
  have h2_fit : Fits w 2 := hfit.of_le (by unfold Instance.wordBound; omega)
  have hn_fit : Fits w I.n := hfit.of_le (by unfold Instance.wordBound; nlinarith)
  have haddr_bound : Fits w (2 + I.n * I.n + 3 * I.n) :=
    hfit.of_le (by unfold Instance.wordBound; nlinarith)
  have hsub_n : Fits w (I.n - 1) := hn_fit.of_le (Nat.sub_le _ _)
  have hmod_n : Fits w (I.n % 2) := h2_fit.of_le (Nat.mod_lt _ (by decide)).le
  have hnn_fit : Fits w (I.n * I.n) := haddr_bound.of_le (by omega)
  have hin_fit : Fits w (I.n * I.n + 2) := haddr_bound.of_le (by omega)
  have hcur_fit : Fits w (I.n * I.n + 2 + I.n) := haddr_bound.of_le (by omega)
  have hnext_fit : Fits w (I.n * I.n + 2 + I.n + I.n) := haddr_bound.of_le (by omega)
  have hmem1 : (Data.init I.encode : Data 22).mem 1 = I.n := I.init_mem_n
  unfold initRegsCode
  wram_exec [hmem1]
  wram_simp [hmem1]; omega

private theorem exec_countHamInit_pow {w : ℕ} (I : Instance) (hfit : I.FitsWidth w) :
    ∃ x1 x2, ExecWithin w initRegsCode (Data.init I.encode) x1 15 ∧
      ExecWithin w (Code.loop (.lt iReg nReg)
        ram[ maskLimit ← maskLimit + maskLimit; iReg ← iReg + oneReg ]) x1 x2 (4 * I.n + 2) ∧
      x2.regs nReg = I.n ∧ x2.regs oneReg = 1 ∧ x2.regs twoReg = 2 ∧
      x2.regs adjBase = 2 ∧ x2.regs nMinus1 = I.n - 1 ∧ x2.regs nParity = I.n % 2 ∧
      x2.regs evenSum = 0 ∧ x2.regs oddSum = 0 ∧ x2.regs maskParity = 0 ∧
      x2.regs inBase = 2 + I.n * I.n ∧ x2.regs curBase = 2 + I.n * I.n + I.n ∧
      x2.regs nextBase = 2 + I.n * I.n + 2 * I.n ∧
      x2.regs maskLimit = 2 ^ I.n ∧ x2.mem = (Data.init I.encode : Data 22).mem := by
  have h1_le := one_le_word_prod I.n
  have hn_fit : Fits w I.n := hfit.of_le (by unfold Instance.wordBound; nlinarith)
  have hpow_fit : Fits w (2 ^ I.n) :=
    hfit.of_le (by
      have hpow_le : 2 ^ I.n ≤ 2 ^ I.n * (I.n + 1) ^ I.n :=
        Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ (by omega))
      unfold Instance.wordBound; omega)
  obtain ⟨x1, hx1, x1n, x11, x12, x1adj, x1nm1, x1np, x1ev, x1od, x1mp, x1in, x1cur, x1next,
    x1ml, x1i, x1m⟩ := exec_initRegs I hfit
  let InvPow (i : ℕ) (d : Data 22) : Prop :=
    i ≤ I.n ∧ d.regs nReg = I.n ∧ d.regs oneReg = 1 ∧ d.regs twoReg = 2 ∧
    d.regs adjBase = 2 ∧ d.regs nMinus1 = I.n - 1 ∧ d.regs nParity = I.n % 2 ∧
    d.regs evenSum = 0 ∧ d.regs oddSum = 0 ∧ d.regs maskParity = 0 ∧
    d.regs inBase = 2 + I.n * I.n ∧ d.regs curBase = 2 + I.n * I.n + I.n ∧
    d.regs nextBase = 2 + I.n * I.n + 2 * I.n ∧
    d.regs maskLimit = 2 ^ i ∧ d.mem = (Data.init I.encode : Data 22).mem
  have hx1_inv : InvPow (x1.regs iReg) x1 := by
    rw [x1i]
    exact ⟨Nat.zero_le _, x1n, x11, x12, x1adj, x1nm1, x1np, x1ev, x1od, x1mp, x1in, x1cur,
      x1next, by simpa using x1ml, x1m⟩
  have hx1_le : x1.regs iReg ≤ I.n := by rw [x1i]; exact Nat.zero_le _
  obtain ⟨x2, hx2, hx2_inv, _⟩ := ExecWithin.loop_count (w := w) (T := 2)
    (body := ram[ maskLimit ← maskLimit + maskLimit; iReg ← iReg + oneReg ])
    InvPow (fun _ h => h.2.1)
    (fun d hd hlt => by
      obtain ⟨hi_le, dn, d1, d2, dadj, dnm1, dnp, dev, dod, dmp, din, dcur, dnext, dml, dm⟩ := hd
      have hi_lt : d.regs iReg < I.n := hlt
      have hfit_2ml : Fits w (d.regs maskLimit + d.regs maskLimit) := by
        rw [dml, ← two_mul, ← pow_succ']
        exact hpow_fit.of_le (Nat.pow_le_pow_right (by decide) (by omega))
      have hf_i : Fits w (d.regs iReg + d.regs oneReg) := by rw [d1]; exact hn_fit.of_le (by omega)
      let z : Data 22 := (d.set maskLimit (d.regs maskLimit + d.regs maskLimit)).set iReg
        (d.regs iReg + d.regs oneReg)
      have hz_ex : ExecWithin w
          (ram[ maskLimit ← maskLimit + maskLimit; iReg ← iReg + oneReg ]) d z 2 := by
        wram_exec
      refine ⟨z, hz_ex, ⟨hi_lt, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · wram_simp [z, dn]
      · wram_simp [z, d1]
      · wram_simp [z, d2]
      · wram_simp [z, dadj]
      · wram_simp [z, dnm1]
      · wram_simp [z, dnp]
      · wram_simp [z, dev]
      · wram_simp [z, dod]
      · wram_simp [z, dmp]
      · wram_simp [z, din]
      · wram_simp [z, dcur]
      · wram_simp [z, dnext]
      · wram_simp [z, d1, dml, ← two_mul, ← pow_succ']
      · exact dm
      · wram_simp [z, d1])
    hx1_le hx1_inv
  have hx2_time : ExecWithin w (Code.loop (.lt iReg nReg)
      ram[ maskLimit ← maskLimit + maskLimit; iReg ← iReg + oneReg ]) x1 x2 (4 * I.n + 2) := by
    refine hx2.mono ?_
    rw [x1i, Nat.sub_zero]; ring_nf; exact le_rfl
  obtain ⟨_, d2n, d21, d22, d2adj, d2nm1, d2np, d2ev, d2od, d2mp, d2in, d2cur, d2next,
    d2ml, d2m⟩ := hx2_inv
  exact ⟨x1, x2, hx1, hx2_time,
    d2n, d21, d22, d2adj, d2nm1, d2np, d2ev, d2od, d2mp, d2in, d2cur, d2next, d2ml, d2m⟩

private theorem exec_zeroStep {w : ℕ} (I : Instance) (hfit : I.FitsWidth w)
    (d : Data 22) (hlt : d.regs iReg < I.n)
    (dn : d.regs nReg = I.n) (d1 : d.regs oneReg = 1) (d2 : d.regs twoReg = 2)
    (dadj : d.regs adjBase = 2) (dnm1 : d.regs nMinus1 = I.n - 1)
    (dnp : d.regs nParity = I.n % 2) (dev : d.regs evenSum = 0)
    (dod : d.regs oddSum = 0) (dmp : d.regs maskParity = 0)
    (din : d.regs inBase = 2 + I.n * I.n)
    (dcur : d.regs curBase = 2 + I.n * I.n + I.n)
    (dnext : d.regs nextBase = 2 + I.n * I.n + 2 * I.n)
    (dml : d.regs maskLimit = 2 ^ I.n)
    (d_adj : memAddrOK I d.mem)
    (d_zero : ∀ u : Fin I.n, u.1 < d.regs iReg → d.mem (2 + I.n * I.n + u.1) = 0) :
    ∃ z, ExecWithin w
        ram[ addr1 ← inBase + iReg; *addr1 ← oddSum; iReg ← iReg + oneReg ] d z 3 ∧
      z.regs iReg ≤ I.n ∧ z.regs nReg = I.n ∧ z.regs oneReg = 1 ∧ z.regs twoReg = 2 ∧
      z.regs adjBase = 2 ∧ z.regs nMinus1 = I.n - 1 ∧ z.regs nParity = I.n % 2 ∧
      z.regs evenSum = 0 ∧ z.regs oddSum = 0 ∧ z.regs maskParity = 0 ∧
      z.regs inBase = 2 + I.n * I.n ∧ z.regs curBase = 2 + I.n * I.n + I.n ∧
      z.regs nextBase = 2 + I.n * I.n + 2 * I.n ∧ z.regs maskLimit = 2 ^ I.n ∧
      memAddrOK I z.mem ∧
      (∀ u : Fin I.n, u.1 < d.regs iReg + 1 → z.mem (2 + I.n * I.n + u.1) = 0) ∧
      z.regs iReg = d.regs iReg + 1 := by
  have h1_le := one_le_word_prod I.n
  have h0_fit : Fits w 0 := hfit.of_le (by unfold Instance.wordBound; omega)
  have hn_fit : Fits w I.n := hfit.of_le (by unfold Instance.wordBound; nlinarith)
  have haddr_bound : Fits w (2 + I.n * I.n + 3 * I.n) :=
    hfit.of_le (by unfold Instance.wordBound; nlinarith)
  have hf_addr : Fits w (d.regs inBase + d.regs iReg) := haddr_bound.of_le (by rw [din]; omega)
  have hf_i : Fits w (d.regs iReg + d.regs oneReg) := by rw [d1]; exact hn_fit.of_le (by omega)
  let z : Data 22 :=
    ((d.set addr1 (2 + I.n * I.n + d.regs iReg)).write
      (2 + I.n * I.n + d.regs iReg) 0).set iReg (d.regs iReg + 1)
  have hz_ex : ExecWithin w
      ram[ addr1 ← inBase + iReg; *addr1 ← oddSum; iReg ← iReg + oneReg ] d z 3 := by
    wram_exec [din, dod, d1]
  refine ⟨z, hz_ex, by wram_simp [z]; omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, by wram_simp [z]⟩
  · wram_simp [z, dn]
  · wram_simp [z, d1]
  · wram_simp [z, d2]
  · wram_simp [z, dadj]
  · wram_simp [z, dnm1]
  · wram_simp [z, dnp]
  · wram_simp [z, dev]
  · wram_simp [z, dod]
  · wram_simp [z, dmp]
  · wram_simp [z, din]
  · wram_simp [z, dcur]
  · wram_simp [z, dnext]
  · wram_simp [z, dml]
  · intro u v
    have hne : 2 + u.1 * I.n + v.1 ≠ 2 + I.n * I.n + d.regs iReg := by
      have := adj_index_lt u v; omega
    wram_simp [z, Data.write, Function.update_of_ne hne]
    exact d_adj u v
  · intro u hu
    by_cases heq : u.1 = d.regs iReg
    · wram_simp [z, Data.write, heq, Function.update_self]
    · have hne : 2 + I.n * I.n + u.1 ≠ 2 + I.n * I.n + d.regs iReg := by omega
      wram_simp [z, Data.write, Function.update_of_ne hne]
      exact d_zero u (by omega)

private theorem exec_countHamInit_zero {w : ℕ} (I : Instance) (hfit : I.FitsWidth w)
    (x2 : Data 22)
    (d2n : x2.regs nReg = I.n) (d21 : x2.regs oneReg = 1) (d22 : x2.regs twoReg = 2)
    (d2adj : x2.regs adjBase = 2) (d2nm1 : x2.regs nMinus1 = I.n - 1)
    (d2np : x2.regs nParity = I.n % 2) (d2ev : x2.regs evenSum = 0)
    (d2od : x2.regs oddSum = 0) (d2mp : x2.regs maskParity = 0)
    (d2in : x2.regs inBase = 2 + I.n * I.n) (d2cur : x2.regs curBase = 2 + I.n * I.n + I.n)
    (d2next : x2.regs nextBase = 2 + I.n * I.n + 2 * I.n)
    (d2ml : x2.regs maskLimit = 2 ^ I.n) (d2adjm : memAddrOK I x2.mem) :
    ∃ x3 x4, ExecWithin w (.op (B := .standard) (.const iReg 0)) x2 x3 1 ∧
      ExecWithin w (Code.loop (.lt iReg nReg)
        ram[ addr1 ← inBase + iReg; *addr1 ← oddSum; iReg ← iReg + oneReg ])
        x3 x4 (5 * I.n + 2) ∧
      x4.regs nReg = I.n ∧ x4.regs nMinus1 = I.n - 1 ∧
      x4.regs oneReg = 1 ∧ x4.regs adjBase = 2 ∧
      x4.regs inBase = 2 + I.n * I.n ∧ x4.regs curBase = 2 + I.n * I.n + I.n ∧
      x4.regs nextBase = 2 + I.n * I.n + 2 * I.n ∧
      x4.regs maskLimit = 2 ^ I.n ∧ x4.regs nParity = I.n % 2 ∧
      x4.regs maskParity = 0 ∧ x4.regs evenSum = 0 ∧ x4.regs oddSum = 0 ∧
      memAddrOK I x4.mem ∧
      (∀ u : Fin I.n, u.1 < I.n → x4.mem (2 + I.n * I.n + u.1) = 0) := by
  have h1_le := one_le_word_prod I.n
  have h0_fit : Fits w 0 := hfit.of_le (by unfold Instance.wordBound; omega)
  let x3 : Data 22 := x2.set iReg 0
  have hx3_ex : ExecWithin w (.op (.const iReg 0)) x2 x3 1 :=
    ExecWithin.const (B := .standard) h0_fit
  let InvZero (i : ℕ) (d : Data 22) : Prop :=
    i ≤ I.n ∧ d.regs nReg = I.n ∧ d.regs oneReg = 1 ∧ d.regs twoReg = 2 ∧
    d.regs adjBase = 2 ∧ d.regs nMinus1 = I.n - 1 ∧ d.regs nParity = I.n % 2 ∧
    d.regs evenSum = 0 ∧ d.regs oddSum = 0 ∧ d.regs maskParity = 0 ∧
    d.regs inBase = 2 + I.n * I.n ∧ d.regs curBase = 2 + I.n * I.n + I.n ∧
    d.regs nextBase = 2 + I.n * I.n + 2 * I.n ∧
    d.regs maskLimit = 2 ^ I.n ∧ memAddrOK I d.mem ∧
    (∀ u : Fin I.n, u.1 < i → d.mem (2 + I.n * I.n + u.1) = 0)
  have hx3_inv : InvZero (x3.regs iReg) x3 := by
    refine ⟨by wram_simp [x3]; exact Nat.zero_le _, by wram_simp [x3, d2n], by wram_simp [x3, d21],
      by wram_simp [x3, d22], by wram_simp [x3, d2adj], by wram_simp [x3, d2nm1],
      by wram_simp [x3, d2np], by wram_simp [x3, d2ev], by wram_simp [x3, d2od],
      by wram_simp [x3, d2mp], by wram_simp [x3, d2in], by wram_simp [x3, d2cur],
      by wram_simp [x3, d2next], by wram_simp [x3, d2ml], d2adjm, fun _ h => by
        wram_simp [x3] at h⟩
  have hx3_le : x3.regs iReg ≤ I.n := by wram_simp [x3]; exact Nat.zero_le _
  obtain ⟨x4, hx4, hx4_inv, _⟩ := ExecWithin.loop_count (w := w) (T := 3)
    (body := ram[ addr1 ← inBase + iReg; *addr1 ← oddSum; iReg ← iReg + oneReg ])
    InvZero (fun _ h => h.2.1)
    (fun d hd hlt => by
      obtain ⟨_, dn, d1, d2, dadj, dnm1, dnp, dev, dod, dmp, din, dcur, dnext, dml, d_adj,
        d_zero⟩ := hd
      have hstep := exec_zeroStep I hfit d hlt dn d1 d2 dadj dnm1 dnp dev dod dmp din dcur dnext
        dml d_adj d_zero
      obtain ⟨z, hz, _, zn, z1, z2, zadj, znm1, znp, zev, zod, zmp, zin, zcur, znext, zml, z_adj,
        z_zero, zi⟩ := hstep
      exact ⟨z, hz, ⟨hlt, zn, z1, z2, zadj, znm1, znp, zev, zod, zmp, zin, zcur, znext, zml,
        z_adj, z_zero⟩, zi⟩)
    hx3_le hx3_inv
  have hx4_time : ExecWithin w (Code.loop (.lt iReg nReg)
      ram[ addr1 ← inBase + iReg; *addr1 ← oddSum; iReg ← iReg + oneReg ]) x3 x4 (5 * I.n + 2) := by
    refine hx4.mono ?_
    have hx3_0 : x3.regs iReg = 0 := by wram_simp [x3]
    rw [hx3_0, Nat.sub_zero]; omega
  obtain ⟨_, h4n, h41, _, h4adj, h4nm1, h4np, h4ev, h4od, h4mp, h4in, h4cur, h4next, h4ml,
    h4adjm, h4z⟩ := hx4_inv
  exact ⟨x3, x4, hx3_ex, hx4_time,
    h4n, h4nm1, h41, h4adj, h4in, h4cur, h4next, h4ml, h4np, h4mp, h4ev, h4od, h4adjm, h4z⟩

private theorem exec_countHamInit {w : ℕ} (I : Instance) (hfit : I.FitsWidth w) :
    ∃ x4, ExecWithin w countHamInitCode (Data.init I.encode) x4 (9 * I.n + 20) ∧
      x4.regs nReg = I.n ∧ x4.regs nMinus1 = I.n - 1 ∧
      x4.regs oneReg = 1 ∧ x4.regs adjBase = 2 ∧
      x4.regs inBase = 2 + I.n * I.n ∧ x4.regs curBase = 2 + I.n * I.n + I.n ∧
      x4.regs nextBase = 2 + I.n * I.n + 2 * I.n ∧
      x4.regs maskLimit = 2 ^ I.n ∧ x4.regs nParity = I.n % 2 ∧
      x4.regs maskParity = 0 ∧ x4.regs evenSum = 0 ∧ x4.regs oddSum = 0 ∧
      memAddrOK I x4.mem ∧
      (∀ u : Fin I.n, u.1 < I.n → x4.mem (2 + I.n * I.n + u.1) = 0) := by
  obtain ⟨x1, x2, hx1, hx2, d2n, d21, d22, d2adj, d2nm1, d2np, d2ev, d2od, d2mp, d2in, d2cur,
    d2next, d2ml, d2m⟩ := exec_countHamInit_pow I hfit
  have d2adjm : memAddrOK I x2.mem := fun u v => by rw [d2m]; exact I.init_mem_adj u v
  obtain ⟨x3, x4, hx3_ex, hx4_time, h4n, h4nm1, h41, h4adj, h4in, h4cur, h4next, h4ml, h4np,
    h4mp, h4ev, h4od, h4adjm, h4z⟩ :=
    exec_countHamInit_zero I hfit x2 d2n d21 d22 d2adj d2nm1 d2np d2ev d2od d2mp d2in d2cur
      d2next d2ml d2adjm
  unfold countHamInitCode
  exact ⟨x4, (hx1.seq (hx2.seq (hx3_ex.seq hx4_time))).mono (by ring_nf; exact le_rfl),
    h4n, h4nm1, h41, h4adj, h4in, h4cur, h4next, h4ml, h4np, h4mp, h4ev, h4od, h4adjm, h4z⟩

private theorem countHam_time_le (n : ℕ) :
    (9 * n + 20) + (1 + (2 ^ n * ((if n = 0 then 16 else 36 * (n ^ 3 + 1)) + 2) + 2 + 1)) ≤
      64 * ((n ^ 3 + 1) * 2 ^ n) - 5 := by
  refine Nat.le_sub_of_add_le ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn_pos
  · simp
  · have hsub : n = (n - 1) + 1 := by omega
    have h2 : 2 ≤ 2 ^ n := by
      rw [hsub, pow_succ]
      have := Nat.one_le_two_pow (n := n - 1)
      omega
    obtain ⟨p, hp⟩ : ∃ p, 2 ^ n = p + 2 := ⟨2 ^ n - 2, by omega⟩
    rw [ite_eq_right hn_pos.ne', hp]
    generalize hm : n - 1 = m
    rw [hm] at hsub
    rw [hsub]
    have hc : 1 ≤ (m + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    have hc3 : m + 1 ≤ (m + 1) ^ 3 := by nlinarith
    nlinarith

private theorem exec_countHamCode {w : ℕ} (I : Instance) (hfit : I.FitsWidth w) :
    ∃ y, ExecWithin w countHamCode (Data.init I.encode) y
        (64 * ((I.n ^ 3 + 1) * 2 ^ I.n) - 5) ∧
      y.regs evenSum = #(hamPaths I.adj) := by
  have h1_le := one_le_word_prod I.n
  have h0_fit : Fits w 0 := hfit.of_le (by unfold Instance.wordBound; omega)
  obtain ⟨x4, hx4, h4n, h4nm1, h41, h4adj, h4in, h4cur, h4next, h4ml, h4np, h4mp, h4ev, h4od,
    h4adjm, h4z⟩ := exec_countHamInit I hfit
  let x5 : Data 22 := x4.set kReg 0
  have hx5_ex : ExecWithin w (.op (.const kReg 0)) x4 x5 1 :=
    ExecWithin.const (B := .standard) h0_fit
  let InvK (k : ℕ) (d : Data 22) : Prop :=
    k ≤ 2 ^ I.n ∧ d.regs nReg = I.n ∧ d.regs nMinus1 = I.n - 1 ∧
    d.regs oneReg = 1 ∧ d.regs adjBase = 2 ∧
    d.regs inBase = 2 + I.n * I.n ∧ d.regs curBase = 2 + I.n * I.n + I.n ∧
    d.regs nextBase = 2 + I.n * I.n + 2 * I.n ∧
    d.regs maskLimit = 2 ^ I.n ∧ d.regs nParity = I.n % 2 ∧
    d.regs maskParity = (maskSet I.n k).card % 2 ∧
    d.regs evenSum = evenPart I k ∧ d.regs oddSum = oddPart I k ∧
    memAddrOK I d.mem ∧
    (∀ u : Fin I.n, d.mem (2 + I.n * I.n + u.1) = if k.testBit u.1 then 1 else 0)
  have hx5_inv : InvK (x5.regs kReg) x5 := by
    refine ⟨by wram_simp [x5]; exact Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, h4adjm, fun u => ?_⟩
    all_goals wram_simp [x5, h4n, h4nm1, h41, h4adj, h4in, h4cur, h4next, h4ml, h4np, h4mp,
      h4ev, h4od]
    · simp [maskSet]
    · simp [evenPart]
    · simp [oddPart]
    · simp [h4z u u.isLt]
  have hx5_le : x5.regs kReg ≤ 2 ^ I.n := by wram_simp [x5]; exact Nat.zero_le _
  obtain ⟨x6, hx6, hx6_inv, _⟩ := ExecWithin.loop_count (w := w)
    (T := if I.n = 0 then 16 else 36 * (I.n ^ 3 + 1)) (body := maskBodyCode)
    InvK (fun _ h => h.2.2.2.2.2.2.2.2.1)
    (fun d hd hlt => by
      obtain ⟨hk_le, dn, dnm1, d1, dadj, din, dcur, dnext, dml, dnp, dmp, dev, dod, d_adj, d_in⟩ :=
        hd
      have hk_lt : d.regs kReg < 2 ^ I.n := hlt
      obtain ⟨y, hy, yn, ynm1, y1, yadj, yin, ycur, ynext, yk, ynp, ymp, yev, yod, yadjm, yinm⟩ :=
        exec_maskBodyCode I (d.regs kReg) hfit hk_lt d dn dnm1 d1 dadj din dcur dnext rfl dnp dmp
          dev dod d_adj d_in
      exact ⟨y, hy, ⟨by omega, yn, ynm1, y1, yadj, yin, ycur, ynext,
        (hy.regs_eq maskBodyCode_preserves_maskLimit).trans dml,
        ynp, ymp, yev, yod, yadjm, yinm⟩, yk⟩)
    hx5_le hx5_inv
  have hx6_time : ExecWithin w (Code.loop (.lt kReg maskLimit) maskBodyCode) x5 x6
      (2 ^ I.n * ((if I.n = 0 then 16 else 36 * (I.n ^ 3 + 1)) + 2) + 2) := by
    refine hx6.mono ?_
    have hx5_0 : x5.regs kReg = 0 := by wram_simp [x5]
    rw [hx5_0, Nat.sub_zero]
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, h6ev, h6od, _⟩ := hx6_inv
  have hsub_eq : evenPart I (2 ^ I.n) - oddPart I (2 ^ I.n) = #(hamPaths I.adj) := by
    have := evenPart_sub_oddPart I
    omega
  have hf_sub : Fits w (x6.regs evenSum - x6.regs oddSum) := by
    rw [h6ev, h6od, hsub_eq]
    have h1 := (part_le_mul I le_rfl).1
    exact hfit.of_le (by unfold Instance.wordBound; omega)
  have hx7_ex : ∃ y, ExecWithin w (.op (.bin .sub evenSum evenSum oddSum)) x6 y 1 ∧
      y = x6.set evenSum (#(hamPaths I.adj)) := by
    refine ⟨x6.set evenSum (x6.regs evenSum - x6.regs oddSum), ExecWithin.bin hf_sub, ?_⟩
    wram_simp [h6ev, h6od, hsub_eq]
  obtain ⟨y, hy_sub, rfl⟩ := hx7_ex
  unfold countHamCode
  refine ⟨x6.set evenSum (#(hamPaths I.adj)),
    (hx4.seq (hx5_ex.seq (hx6_time.seq hy_sub))).mono (countHam_time_le I.n), ?_⟩
  wram_simp

private theorem exec_decideHamCode {w : ℕ} (I : Instance) (hfit : I.FitsWidth w) :
    ∃ y, ExecWithin w decideHamCode (Data.init I.encode) y
        (64 * ((I.n ^ 3 + 1) * 2 ^ I.n) - 1) ∧
      y.regs evenSum = if (hamPaths I.adj).Nonempty then 1 else 0 := by
  have h1_le := one_le_word_prod I.n
  have h1_pow : 1 ≤ (I.n ^ 3 + 1) * 2 ^ I.n := Nat.mul_pos (by omega) Nat.one_le_two_pow
  have h0_fit : Fits w 0 := hfit.of_le (by unfold Instance.wordBound; omega)
  have h1_fit : Fits w 1 := hfit.of_le (by unfold Instance.wordBound; omega)
  obtain ⟨y1, hy1, hy1_ans⟩ := exec_countHamCode I hfit
  let y2 : Data 22 := y1.set tmpReg 0
  have hy2_ex : ExecWithin w (.op (.const tmpReg 0)) y1 y2 1 :=
    ExecWithin.const (B := .standard) h0_fit
  unfold decideHamCode
  by_cases hne : (hamPaths I.adj).Nonempty
  · have hpos : #(hamPaths I.adj) ≠ 0 := (Finset.card_pos.2 hne).ne'
    have hneg : ¬ Cond.Holds (.eq evenSum tmpReg) y2 := by
      change y2.regs evenSum ≠ y2.regs tmpReg
      wram_simp [y2, hy1_ans]
      exact hpos
    let y3 : Data 22 := y2.set evenSum 1
    have hy3_ex : ExecWithin w (.op (.const evenSum 1)) y2 y3 1 :=
      ExecWithin.const (B := .standard) h1_fit
    refine ⟨y3, (hy1.seq (hy2_ex.seq (ExecWithin.branch_neg hneg hy3_ex))).mono (by omega), ?_⟩
    simp [y3, y2, hne]
  · have h0 : #(hamPaths I.adj) = 0 := by
      rw [Finset.card_eq_zero]
      exact Finset.not_nonempty_iff_eq_empty.1 hne
    have hpos_cond : Cond.Holds (.eq evenSum tmpReg) y2 := by
      change y2.regs evenSum = y2.regs tmpReg
      wram_simp [y2, hy1_ans, h0]
    let y3 : Data 22 := y2.set evenSum 0
    have hy3_ex : ExecWithin w (.op (.const evenSum 0)) y2 y3 1 :=
      ExecWithin.const (B := .standard) h0_fit
    refine ⟨y3, (hy1.seq (hy2_ex.seq (ExecWithin.branch_pos hpos_cond hy3_ex))).mono (by omega), ?_⟩
    simp [y3, y2, hne]

/-- Standard-basis `ComputesInTime` certificate for `program`. -/
theorem computesInTime_program :
    program.ComputesInTime (fun _ => Instance.encode)
      (fun I _ => 64 * ((I.n ^ 3 + 1) * 2 ^ I.n))
      Instance.FitsWidth (fun I => #(hamPaths I.adj)) := by
  have hsub := countHamCode.computesInTime_program evenSum
    (encode := fun _ => Instance.encode)
    (time := fun I _ => 64 * ((I.n ^ 3 + 1) * 2 ^ I.n) - 1)
    fun I w hfit _ => by
      obtain ⟨y, hy, hy_ans⟩ := exec_countHamCode I hfit
      exact ⟨y, hy.mono (by omega), hy_ans⟩
  intro I w hfit hw
  obtain ⟨steps, hexec, hle⟩ := hsub I w hfit hw
  dsimp only at hle ⊢
  have h2 : 1 ≤ (I.n ^ 3 + 1) * 2 ^ I.n := Nat.mul_pos (by omega) Nat.one_le_two_pow
  exact ⟨steps, hexec, by omega⟩

/-- Concrete Word-RAM execution bound for Karp–Bax Hamiltonian-path counting
(`≤ 64 · ((n³ + 1) · 2 ^ n)` standard-basis instructions). -/
theorem program_spec {I : Instance} {w : ℕ} (hfit : I.FitsWidth w) :
    ∃ steps ≤ 64 * ((I.n ^ 3 + 1) * 2 ^ I.n),
      Executes w program (.init I.encode) #(hamPaths I.adj) steps := by
  obtain ⟨steps, hexec, hle⟩ := computesInTime_program I w hfit (I.inputFits hfit)
  exact ⟨steps, hle, hexec⟩

/-- Standard-basis `ComputesInTime` certificate for `decideProgram`. -/
theorem computesInTime_decideProgram :
    decideProgram.ComputesInTime (fun _ => Instance.encode)
      (fun I _ => 64 * ((I.n ^ 3 + 1) * 2 ^ I.n))
      Instance.FitsWidth (fun I => if (hamPaths I.adj).Nonempty then 1 else 0) := by
  have hsub := decideHamCode.computesInTime_program evenSum
    (encode := fun _ => Instance.encode)
    (time := fun I _ => 64 * ((I.n ^ 3 + 1) * 2 ^ I.n) - 1)
    fun I w hfit _ => exec_decideHamCode I hfit
  intro I w hfit hw
  obtain ⟨steps, hexec, hle⟩ := hsub I w hfit hw
  dsimp only at hle ⊢
  have h2 : 1 ≤ (I.n ^ 3 + 1) * 2 ^ I.n := Nat.mul_pos (by omega) Nat.one_le_two_pow
  exact ⟨steps, hexec, by omega⟩

/-- Concrete Word-RAM execution bound for deciding whether `I` has a Hamiltonian path
(`1` iff `(hamPaths I.adj).Nonempty`, `0` otherwise). -/
theorem decideProgram_spec {I : Instance} {w : ℕ} (hfit : I.FitsWidth w) :
    ∃ steps ≤ 64 * ((I.n ^ 3 + 1) * 2 ^ I.n),
      Executes w decideProgram (.init I.encode)
        (if (hamPaths I.adj).Nonempty then 1 else 0) steps := by
  obtain ⟨steps, hexec, hle⟩ := computesInTime_decideProgram I w hfit (I.inputFits hfit)
  exact ⟨steps, hle, hexec⟩

private theorem not_readsWidth_countHamCode : ¬ countHamCode.ReadsWidth := by
  have hcopy : ∀ s d, ¬ (copyVec s d).ReadsWidth := fun s d => by
    simp only [copyVec, Code.ReadsWidth, Op.ReadsWidth, Op.bin, not_or]
    repeat (first | constructor | decide)
  have hcell : ¬ stepCellCode.ReadsWidth := by
    simp only [stepCellCode, Code.ReadsWidth, Op.ReadsWidth, Op.bin, not_or]
    repeat (first | constructor | decide)
  have hstep : ¬ stepVecCode.ReadsWidth := by
    simp only [stepVecCode, Code.ReadsWidth, Op.ReadsWidth, not_or]
    exact ⟨by decide, hcell⟩
  have hrounds : ¬ roundsCode.ReadsWidth := by
    simp only [roundsCode, Code.ReadsWidth, Op.ReadsWidth, Op.bin, not_or]
    exact ⟨by decide, hstep, hcopy _ _, by decide⟩
  have hsum : ¬ sumVecCode.ReadsWidth := by
    simp only [sumVecCode, Code.ReadsWidth, Op.ReadsWidth, Op.bin, not_or]
    repeat (first | constructor | decide)
  have hodo : ¬ odometerCode.ReadsWidth := by
    simp only [odometerCode, Code.ReadsWidth, Op.ReadsWidth, Op.bin, not_or]
    repeat (first | constructor | decide)
  have hmask : ¬ maskBodyCode.ReadsWidth := by
    simp only [maskBodyCode, Code.ReadsWidth, Op.ReadsWidth, Op.bin, not_or]
    exact ⟨by decide, ⟨⟨hcopy _ _, hrounds, hsum⟩, by decide⟩, ⟨by decide, by decide⟩, hodo,
      by decide⟩
  have hinit : ¬ countHamInitCode.ReadsWidth := by
    have hregs : ¬ initRegsCode.ReadsWidth := by
      simp only [initRegsCode, Code.ReadsWidth, Op.ReadsWidth, Op.bin, not_or]
      repeat (first | constructor | decide)
    simp only [countHamInitCode, Code.ReadsWidth, Op.ReadsWidth, Op.bin, not_or]
    exact ⟨hregs, by decide, by decide, by decide⟩
  simp only [countHamCode, Code.ReadsWidth, Op.ReadsWidth, Op.bin, not_or]
  exact ⟨hinit, by decide, hmask, by decide⟩

private theorem isRandFree_countHamCode : countHamCode.IsRandFree := by
  have hcopy : ∀ s d, (copyVec s d).IsRandFree := fun s d => by
    simp only [copyVec, Code.IsRandFree]; tauto
  have hcell : stepCellCode.IsRandFree := by
    simp only [stepCellCode, Code.IsRandFree]; tauto
  have hstep : stepVecCode.IsRandFree := ⟨trivial, hcell⟩
  have hrounds : roundsCode.IsRandFree := ⟨trivial, hstep, hcopy _ _, trivial⟩
  have hsum : sumVecCode.IsRandFree := by
    simp only [sumVecCode, Code.IsRandFree]; tauto
  have hodo : odometerCode.IsRandFree := by
    simp only [odometerCode, Code.IsRandFree]; tauto
  have hmask : maskBodyCode.IsRandFree :=
    ⟨trivial, ⟨⟨hcopy _ _, hrounds, hsum⟩, trivial⟩, ⟨trivial, trivial⟩, hodo, trivial⟩
  have hinit : countHamInitCode.IsRandFree := by
    have hregs : initRegsCode.IsRandFree := by
      simp only [initRegsCode, Code.IsRandFree]; tauto
    exact ⟨hregs, by simp only [Code.IsRandFree]; tauto, trivial,
      by simp only [Code.IsRandFree]; tauto⟩
  exact ⟨hinit, trivial, hmask, trivial⟩

/-- `program` never reads the machine word size. -/
theorem not_readsWidth_program : ¬ program.ReadsWidth := by
  rw [program]
  exact Code.not_readsWidth_program not_readsWidth_countHamCode _

/-- `program` is deterministic (no `rand` instruction). -/
theorem isRandFree_program : program.IsRandFree := by
  rw [program, Code.isRandFree_program]
  exact isRandFree_countHamCode

/-- `decideProgram` never reads the machine word size. -/
theorem not_readsWidth_decideProgram : ¬ decideProgram.ReadsWidth := by
  rw [decideProgram]
  refine Code.not_readsWidth_program ?_ _
  simp only [decideHamCode, Code.ReadsWidth, Op.ReadsWidth, not_or]
  exact ⟨not_readsWidth_countHamCode, by decide, by decide, by decide⟩

/-- `decideProgram` is deterministic (no `rand` instruction). -/
theorem isRandFree_decideProgram : decideProgram.IsRandFree := by
  rw [decideProgram, Code.isRandFree_program]
  exact ⟨isRandFree_countHamCode, trivial, trivial, trivial⟩

end Cslib.Algorithms.WordRAM.HamiltonianCount
