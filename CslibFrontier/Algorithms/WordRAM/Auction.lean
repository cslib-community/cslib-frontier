/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Assignment.Auction
public import CslibFrontier.Computability.WordRAM.ListOutput
public import CslibFrontier.Computability.WordRAM.Signed.Encoding
import CslibFrontier.Computability.WordRAM.Allocation
import CslibFrontier.Computability.WordRAM.CountingLoop
import CslibFrontier.Computability.WordRAM.SymbolicExec
import CslibFrontier.Foundations.Data.List.RowMajor
import CslibFrontier.Foundations.Data.Matrix.PairChunks
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith

/-!
# Bertsekas's auction algorithm on the word RAM

This file implements and proves machine-level running-time bounds on the standard-basis word RAM
(`Basis.standard`) for Bertsekas's Gauss–Seidel `ε`-auction algorithm
(`Cslib.Algorithms.Lean.Assignment.auction` and `Cslib.Algorithms.Lean.Assignment.scaledAuction`):

1. **In-memory unsigned cost core (`coreCode`, `core_exec`).** Given an `n × n` unsigned cost
   matrix `C : Fin n × Fin n → ℕ` bounded by `W` stored row-major at `bC` and a positive integer
   increment `ε > 0`, `coreCode` maintains `owner[0..n)`, nonnegative integer prices `price[0..n)`,
   and the reversed unassigned-person stack `stack[0..sp)` in `O(1)` per push/pop and `O(n)` per
   bid. By `AuctionInv.price_le` and `price_nonneg_bidStep`, all active prices stay in
   `[0, W + ε]`, reduced costs stay in `[0, 2 W + ε]`, and unsigned bid updates never underflow or
   overflow at any word width satisfying `Fits w (matBase + 2 n² + 4 n + 2 W + 2 ε + 4)`, executing
   in `(auction c ε).bids * (28 n + 30) + 17 n + 12` instructions.
2. **Unscaled `ε`-auction from `State.init` (`EpsInstance`, `epsAuctionProgram`).** Scans the
   signed input costs for a magnitude bound `M ≤ inst.maxMag`, shifts every entry by `+ M` into
   `[0, 2 M]` (leaving the entire trajectory unchanged by `auction_add_const`), runs `coreCode`,
   and scatters the permutation `auctionPerm` to length-prefixed output memory in
   `epsAuctionTime n C eps = O(n² (C / ε + 1))` instructions ([Bertsekas1988], §1) whenever `C`
   bounds the row cost ranges (`inst.rowSpread` unconditionally) and `Fits w inst.wordBound`
   (`w = O(log n + log M + log ε)`).
3. **Exact `(n + 1)`-scaled integer auction from `State.init` (`Instance`, `scaledAuctionProgram`,
   `scaledMinCostProgram`).** Scales shifted costs by `n + 1` with `ε = 1` ([Bertsekas1988], §3),
   computing the exact minimum-cost assignment `scaledAuctionPerm` (`sum_scaledAuctionPerm_le`) and
   `Signed.encode` of its minimum cost in `scaledAuctionTime n C = O(n³ C + n²)` instructions at
   logarithmic word width `Fits w inst.wordBound` (`w = O(log n + log M)`).

## Main definitions

* `Cslib.Algorithms.WordRAM.Auction.EpsInstance`,
  `Cslib.Algorithms.WordRAM.Auction.Instance`: problem instances for the `ε`-auction and exact
  scaled integer auction, with their encodings, `maxMag`, `rowSpread`, `wordBound`, and outputs.
* `Cslib.Algorithms.WordRAM.Auction.BaseRegs`,
  `Cslib.Algorithms.WordRAM.Auction.CostMem`: register frame and row-major matrix assertion for
  `coreCode`.
* `Cslib.Algorithms.WordRAM.Auction.coreCode`,
  `Cslib.Algorithms.WordRAM.Auction.epsAuctionProgram`,
  `Cslib.Algorithms.WordRAM.Auction.scaledAuctionProgram`,
  `Cslib.Algorithms.WordRAM.Auction.scaledMinCostProgram`: structured and flat word-RAM programs.
* `Cslib.Algorithms.WordRAM.Auction.epsAuctionTime`,
  `Cslib.Algorithms.WordRAM.Auction.scaledAuctionTime`: instruction bounds.

## Main results

* `Cslib.Algorithms.WordRAM.Auction.core_exec`: in-memory execution of `coreCode` matching
  `auction`.
* `Cslib.Algorithms.WordRAM.Auction.executesList_epsAuction`,
  `Cslib.Algorithms.WordRAM.Auction.computesListInTime_epsAuction`: `O(n² (C / ε + 1))` `ε`-auction
  running-time bounds (whose output satisfies `sum_auctionPerm_le` and
  `isEpsCompSlack_auctionPerm`).
* `Cslib.Algorithms.WordRAM.Auction.executesList_scaledAuction`,
  `Cslib.Algorithms.WordRAM.Auction.computesListInTime_scaledAuction`,
  `Cslib.Algorithms.WordRAM.Auction.executes_scaledMinCost`,
  `Cslib.Algorithms.WordRAM.Auction.computesInTime_scaledMinCost`: `O(n³ C + n²)` exact assignment
  and minimum-cost bounds (optimal by `sum_scaledAuctionPerm_le`).
* `Cslib.Algorithms.WordRAM.Auction.not_readsWidth_epsAuctionProgram`,
  `Cslib.Algorithms.WordRAM.Auction.not_readsWidth_scaledAuctionProgram`,
  `Cslib.Algorithms.WordRAM.Auction.not_readsWidth_scaledMinCostProgram`: width-independence
  (`¬ Program.ReadsWidth`) and `IsRandFree` certificates.

## References

* [Bertsekas1979]
* [Bertsekas1988]
* [Bertsekas1998]
-/

public section

namespace Cslib.Algorithms.WordRAM.Auction

open Cslib.WordRAM
open Cslib.Algorithms.Lean.Assignment

/-! ## Section 1: Problem instances and encodings -/

/-- Problem instance for exact minimum-cost integer assignment via Bertsekas's `(n + 1)`-scaled
auction (`scaledAuction`, `ε = 1`). -/
structure Instance where
  /-- Common number of persons and objects. -/
  n : ℕ
  /-- Signed integer assignment cost `Fin n × Fin n → ℤ`. -/
  cost : Fin n × Fin n → ℤ

namespace Instance

/-- Maximum entry magnitude `max_{i, j} |cost (i, j)|` (`0` when `n = 0`). -/
@[expose] def maxMag (inst : Instance) : ℕ :=
  Finset.univ.sup fun p : Fin inst.n × Fin inst.n => (inst.cost p).natAbs

/-- Maximum within-row cost difference `max_{i, j, k} (cost (i, k) - cost (i, j))` (`0` when
`n = 0`). -/
@[expose] def rowSpread (inst : Instance) : ℕ :=
  Finset.univ.sup fun i : Fin inst.n =>
    Finset.univ.sup fun j : Fin inst.n =>
      Finset.univ.sup fun k : Fin inst.n =>
        (inst.cost (i, k) - inst.cost (i, j)).toNat

theorem natAbs_cost_le_maxMag (inst : Instance) (i j : Fin inst.n) :
    (inst.cost (i, j)).natAbs ≤ inst.maxMag :=
  Finset.le_sup (f := fun p : Fin inst.n × Fin inst.n => (inst.cost p).natAbs)
    (Finset.mem_univ (i, j))

theorem sub_le_rowSpread (inst : Instance) (i j k : Fin inst.n) :
    inst.cost (i, k) - inst.cost (i, j) ≤ (inst.rowSpread : ℤ) := by
  have hk : (inst.cost (i, k) - inst.cost (i, j)).toNat ≤
      Finset.univ.sup fun k' => (inst.cost (i, k') - inst.cost (i, j)).toNat :=
    Finset.le_sup (f := fun k' => (inst.cost (i, k') - inst.cost (i, j)).toNat)
      (Finset.mem_univ k)
  have hj : (Finset.univ.sup fun k' => (inst.cost (i, k') - inst.cost (i, j)).toNat) ≤
      Finset.univ.sup fun j' => Finset.univ.sup fun k' =>
        (inst.cost (i, k') - inst.cost (i, j')).toNat :=
    Finset.le_sup (f := fun j' => Finset.univ.sup fun k' =>
      (inst.cost (i, k') - inst.cost (i, j')).toNat) (Finset.mem_univ j)
  have hi : (Finset.univ.sup fun j' => Finset.univ.sup fun k' =>
      (inst.cost (i, k') - inst.cost (i, j')).toNat) ≤ inst.rowSpread :=
    Finset.le_sup (f := fun i' => Finset.univ.sup fun j' => Finset.univ.sup fun k' =>
      (inst.cost (i', k') - inst.cost (i', j')).toNat) (Finset.mem_univ i)
  exact (Int.self_le_toNat _).trans (Nat.cast_le.mpr (hk.trans (hj.trans hi)))

/-- Row-major word encoding `n :: matrixWords` (`1 + n * n` words). -/
@[expose] def encode (inst : Instance) : List ℕ :=
  inst.n :: (List.finRange inst.n).flatMap fun i =>
    (List.finRange inst.n).map fun j => Signed.encode (inst.cost (i, j))

/-- Word-value envelope covering input words, workspace addresses, `(n + 1)`-scaled shifted costs,
prices, reduced costs, and accumulated total assignment cost (`w = O(log n + log M)`). -/
@[expose] def wordBound (inst : Instance) : ℕ :=
  2 * (inst.n * inst.n) + 5 * inst.n + 4 * (inst.n + 1) * inst.maxMag + 10

/-- Optimal assignment list `[obj_0, …, obj_{n - 1}]` computed by `scaledAuction`
(`scaledAuctionPerm inst.cost`; optimal by `sum_scaledAuctionPerm_le`). -/
@[expose] def assignment (inst : Instance) : List ℕ :=
  (List.finRange inst.n).map fun i => (scaledAuctionPerm inst.cost i).val

/-- Minimum assignment cost `∑ i, inst.cost (i, scaledAuctionPerm inst.cost i)`. -/
@[expose] def minCost (inst : Instance) : ℤ :=
  ∑ i : Fin inst.n, inst.cost (i, scaledAuctionPerm inst.cost i)

/-- Minimum assignment cost encoded via `Signed.encode`. -/
@[expose] def encodedMinCost (inst : Instance) : ℕ :=
  Signed.encode inst.minCost

@[simp] theorem length_assignment (inst : Instance) : inst.assignment.length = inst.n := by
  simp [assignment]

private theorem getElem_assignment (inst : Instance) (i : Fin inst.n) :
    inst.assignment[i.val]'(by simp [assignment]) = (scaledAuctionPerm inst.cost i).val := by
  simp [assignment]

theorem encode_length (inst : Instance) : inst.encode.length = 1 + inst.n * inst.n := by
  simp only [encode, List.length_cons, List.length_flatMap, List.length_map, List.length_finRange,
    List.map_const', List.sum_replicate, smul_eq_mul]
  omega

private theorem init_mem_n {reg : ℕ} (inst : Instance) :
    (Data.init inst.encode : Data reg).mem 1 = inst.n := rfl

private theorem init_mem_cost {reg : ℕ} (inst : Instance) (i j : Fin inst.n) :
    (Data.init inst.encode : Data reg).mem (2 + (i.val * inst.n + j.val)) =
      Signed.encode (inst.cost (i, j)) := by
  let g : Fin inst.n → List ℕ := fun i' =>
    (List.finRange inst.n).map fun j' => Signed.encode (inst.cost (i', j'))
  have h := List.getElem?_flatMap_mul_add (List.finRange inst.n) g inst.n
    (fun _ _ => by simp [g]) (show i.val < (List.finRange inst.n).length by simp) j.isLt
  rw [show 2 + (i.val * inst.n + j.val) = (i.val * inst.n + j.val) + 1 + 1 by omega,
    Data.init_mem_succ, encode, List.getD_cons_succ, List.getD_eq_getElem?_getD, h]
  simp [g]

theorem inputFits_encode {w : ℕ} (inst : Instance) (hw : Fits w inst.wordBound) :
    InputFits w inst.encode := by
  refine ⟨hw.of_le (by rw [inst.encode_length]; unfold wordBound; nlinarith), fun x hx => ?_⟩
  simp only [encode, List.mem_cons, List.mem_flatMap, List.mem_finRange, true_and,
    List.mem_map] at hx
  rcases hx with rfl | ⟨i, j, rfl⟩
  · exact hw.of_le (by unfold wordBound; nlinarith)
  · have hm := inst.natAbs_cost_le_maxMag i j
    have he : Signed.encode (inst.cost (i, j)) ≤ 2 * inst.maxMag + 1 := by
      unfold Signed.encode
      split_ifs <;> omega
    exact hw.of_le (by unfold wordBound; nlinarith)

end Instance

/-- Problem instance for Bertsekas's Gauss–Seidel `ε`-auction on an `n × n` integer cost matrix. -/
structure EpsInstance where
  /-- Common number of persons and objects. -/
  n : ℕ
  /-- Bidding increment `ε` (admitted when `0 < eps`). -/
  eps : ℕ
  /-- Signed integer assignment cost `Fin n × Fin n → ℤ`. -/
  cost : Fin n × Fin n → ℤ

namespace EpsInstance

/-- Underlying `n × n` cost matrix instance. -/
abbrev toInstance (inst : EpsInstance) : Instance := ⟨inst.n, inst.cost⟩

/-- Maximum entry magnitude `max_{i, j} |cost (i, j)|` (`0` when `n = 0`). -/
abbrev maxMag (inst : EpsInstance) : ℕ := inst.toInstance.maxMag

/-- Maximum within-row cost difference `max_{i, j, k} (cost (i, k) - cost (i, j))` (`0` when
`n = 0`). -/
abbrev rowSpread (inst : EpsInstance) : ℕ := inst.toInstance.rowSpread

/-- Row-major word encoding `n :: eps :: matrixWords` (`2 + n * n` words). -/
@[expose] def encode (inst : EpsInstance) : List ℕ :=
  inst.n :: inst.eps :: inst.toInstance.encode.tail

/-- Word-value envelope covering input words, workspace addresses, shifted costs, reduced costs,
and object prices (`w = O(log n + log M + log ε)`). -/
@[expose] def wordBound (inst : EpsInstance) : ℕ :=
  2 * (inst.n * inst.n) + 5 * inst.n + 4 * inst.maxMag + 2 * inst.eps + 8

/-- Person-indexed assignment list `[obj_0, …, obj_{n - 1}]` computed by
`auction inst.cost inst.eps` (`auctionPerm` when `0 < inst.eps`; `n * eps`-optimal by
`sum_auctionPerm_le`). -/
@[expose] def assignment (inst : EpsInstance) : List ℕ :=
  (List.finRange inst.n).map fun i => ((auction inst.cost (inst.eps : ℤ)).objectOf i).val

@[simp] theorem length_assignment (inst : EpsInstance) : inst.assignment.length = inst.n := by
  simp [assignment]

theorem encode_length (inst : EpsInstance) : inst.encode.length = 2 + inst.n * inst.n := by
  have htail : inst.toInstance.encode.tail.length = inst.n * inst.n := by
    have := inst.toInstance.encode_length
    simp only [Instance.encode, List.length_cons] at this
    simp only [Instance.encode, List.tail_cons]
    omega
  simp only [encode, List.length_cons, htail]
  omega

private theorem init_mem_n {reg : ℕ} (inst : EpsInstance) :
    (Data.init inst.encode : Data reg).mem 1 = inst.n := rfl

private theorem init_mem_eps {reg : ℕ} (inst : EpsInstance) :
    (Data.init inst.encode : Data reg).mem 2 = inst.eps := rfl

private theorem init_mem_cost {reg : ℕ} (inst : EpsInstance) (i j : Fin inst.n) :
    (Data.init inst.encode : Data reg).mem (3 + (i.val * inst.n + j.val)) =
      Signed.encode (inst.cost (i, j)) := by
  have hbase := inst.toInstance.init_mem_cost (reg := reg) i j
  rw [show 3 + (i.val * inst.n + j.val) = (i.val * inst.n + j.val) + 1 + 1 + 1 by omega,
    Data.init_mem_succ, encode, List.getD_cons_succ, List.getD_cons_succ]
  rw [show 2 + (i.val * inst.n + j.val) = (i.val * inst.n + j.val) + 1 + 1 by omega,
    Data.init_mem_succ, Instance.encode, List.getD_cons_succ] at hbase
  exact hbase

theorem inputFits_encode {w : ℕ} (inst : EpsInstance) (hw : Fits w inst.wordBound) :
    InputFits w inst.encode := by
  refine ⟨hw.of_le (by rw [inst.encode_length]; unfold wordBound; nlinarith), fun x hx => ?_⟩
  simp only [encode, Instance.encode, List.tail_cons, List.mem_cons, List.mem_flatMap,
    List.mem_finRange, true_and, List.mem_map] at hx
  rcases hx with rfl | rfl | ⟨i, j, rfl⟩
  · exact hw.of_le (by unfold wordBound; nlinarith)
  · exact hw.of_le (by unfold wordBound; nlinarith)
  · have hm : (inst.cost (i, j)).natAbs ≤ inst.maxMag := inst.toInstance.natAbs_cost_le_maxMag i j
    have he : Signed.encode (inst.cost (i, j)) ≤ 2 * inst.maxMag + 1 := by
      unfold Signed.encode
      split_ifs <;> omega
    exact hw.of_le (by unfold wordBound; nlinarith)

end EpsInstance

/-! ## Section 2: Registers and memory layout -/

namespace Reg

/-- Constant `0`. -/
abbrev zero : Fin 26 := ⟨0, by decide⟩
/-- Constant `1`. -/
abbrev one : Fin 26 := ⟨1, by decide⟩
/-- Constant `2`. -/
abbrev two : Fin 26 := ⟨2, by decide⟩
/-- Dimension `n`. -/
abbrev rn : Fin 26 := ⟨3, by decide⟩
/-- Product `n * n`. -/
abbrev rnn : Fin 26 := ⟨4, by decide⟩
/-- Bidding increment `ε`. -/
abbrev reps : Fin 26 := ⟨5, by decide⟩
/-- Cost scaling factor (`1` or `n + 1`). -/
abbrev rscale : Fin 26 := ⟨6, by decide⟩
/-- Scanned entry magnitude bound `M`. -/
abbrev rM : Fin 26 := ⟨7, by decide⟩
/-- Start address of input encoded matrix (`3` or `2`). -/
abbrev matBaseReg : Fin 26 := ⟨8, by decide⟩
/-- Base address of working unsigned `n × n` matrix `C[0..n*n)`. -/
abbrev bC : Fin 26 := ⟨9, by decide⟩
/-- Base address of `owner[0..n)`. -/
abbrev bOwner : Fin 26 := ⟨10, by decide⟩
/-- Base address of `price[0..n)`. -/
abbrev bPrice : Fin 26 := ⟨11, by decide⟩
/-- Base address of reversed unassigned stack `stack[0..n)`. -/
abbrev bStack : Fin 26 := ⟨12, by decide⟩
/-- Output list header address register. -/
abbrev outBase : Fin 26 := ⟨13, by decide⟩
/-- Stack pointer / scalar output register. -/
abbrev sp : Fin 26 := ⟨14, by decide⟩
private abbrev curI : Fin 26 := ⟨15, by decide⟩
private abbrev rowBase : Fin 26 := ⟨16, by decide⟩
private abbrev bestJ : Fin 26 := ⟨17, by decide⟩
private abbrev bestVal : Fin 26 := ⟨18, by decide⟩
private abbrev hasSecond : Fin 26 := ⟨19, by decide⟩
private abbrev secondVal : Fin 26 := ⟨20, by decide⟩
private abbrev idx : Fin 26 := ⟨21, by decide⟩
private abbrev addr : Fin 26 := ⟨22, by decide⟩
private abbrev val : Fin 26 := ⟨23, by decide⟩
private abbrev val2 : Fin 26 := ⟨24, by decide⟩
private abbrev tmp : Fin 26 := ⟨25, by decide⟩

end Reg

open Reg

private def encodeOptFin {n : ℕ} : Option (Fin n) → ℕ
  | some i => i.val
  | none => n

/-- Row-major unsigned `n × n` cost matrix `C` stored at `base`. -/
structure CostMem {n : ℕ} (base : ℕ) (C : Fin n × Fin n → ℕ) (mem : ℕ → ℕ) : Prop where
  /-- Entry `(i, j)` lies at `base + i * n + j`. -/
  hentry : ∀ i j : Fin n, mem (base + (i.val * n + j.val)) = C (i, j)

private theorem CostMem.of_outside {n base : ℕ} {C : Fin n × Fin n → ℕ} {mem mem' : ℕ → ℕ}
    (h : CostMem base C mem) (hf : ∀ a, base ≤ a ∧ a < base + n * n → mem' a = mem a) :
    CostMem base C mem' where
  hentry i j := by
    have hlt : i.val * n + j.val < n * n := Cslib.Matrix.pairIndex_lt (i, j)
    exact (hf _ ⟨by omega, by omega⟩).trans (h.hentry i j)

/-- Read-only constant and workspace pointer registers (`0 .. 13`) for `coreCode`. -/
structure BaseRegs (n matBase eps scale M : ℕ) (x : Data 26) : Prop where
  /-- `zero = 0`. -/
  hzero : x.regs zero = 0
  /-- `one = 1`. -/
  hone : x.regs one = 1
  /-- `two = 2`. -/
  htwo : x.regs two = 2
  /-- `rn = n`. -/
  hrn : x.regs rn = n
  /-- `rnn = n * n`. -/
  hrnn : x.regs rnn = n * n
  /-- `reps = eps`. -/
  hreps : x.regs reps = eps
  /-- `rscale = scale`. -/
  hrscale : x.regs rscale = scale
  /-- `rM = M`. -/
  hrM : x.regs rM = M
  /-- `matBaseReg = matBase`. -/
  hmatBase : x.regs matBaseReg = matBase
  /-- `bC = matBase + n * n`. -/
  hbC : x.regs bC = matBase + n * n
  /-- `bOwner = matBase + 2 * (n * n)`. -/
  hbOwner : x.regs bOwner = matBase + 2 * (n * n)
  /-- `bPrice = matBase + 2 * (n * n) + n`. -/
  hbPrice : x.regs bPrice = matBase + 2 * (n * n) + n
  /-- `bStack = matBase + 2 * (n * n) + 2 * n`. -/
  hbStack : x.regs bStack = matBase + 2 * (n * n) + 2 * n
  /-- `outBase = matBase + 2 * (n * n) + 3 * n`. -/
  houtBase : x.regs outBase = matBase + 2 * (n * n) + 3 * n

private theorem BaseRegs.of_eq {n matBase eps scale M : ℕ} {x y : Data 26}
    (hb : BaseRegs n matBase eps scale M x)
    (heq : ∀ i : Fin 26, i.val < 14 → y.regs i = x.regs i) :
    BaseRegs n matBase eps scale M y where
  hzero := (heq zero (by decide)).trans hb.hzero
  hone := (heq one (by decide)).trans hb.hone
  htwo := (heq two (by decide)).trans hb.htwo
  hrn := (heq rn (by decide)).trans hb.hrn
  hrnn := (heq rnn (by decide)).trans hb.hrnn
  hreps := (heq reps (by decide)).trans hb.hreps
  hrscale := (heq rscale (by decide)).trans hb.hrscale
  hrM := (heq rM (by decide)).trans hb.hrM
  hmatBase := (heq matBaseReg (by decide)).trans hb.hmatBase
  hbC := (heq bC (by decide)).trans hb.hbC
  hbOwner := (heq bOwner (by decide)).trans hb.hbOwner
  hbPrice := (heq bPrice (by decide)).trans hb.hbPrice
  hbStack := (heq bStack (by decide)).trans hb.hbStack
  houtBase := (heq outBase (by decide)).trans hb.houtBase

private def OwnerMem {n : ℕ} (base : ℕ) (owner : Fin n → Option (Fin n)) (mem : ℕ → ℕ) : Prop :=
  ∀ j : Fin n, mem (base + j.val) = encodeOptFin (owner j)

private def PriceMem {n : ℕ} (base : ℕ) (price : Fin n → ℤ) (mem : ℕ → ℕ) : Prop :=
  ∀ j : Fin n, mem (base + j.val) = (price j).toNat

private def StackMem {n : ℕ} (base : ℕ) (free : List (Fin n)) (x : Data 26) : Prop :=
  x.regs sp = free.length ∧
    ∀ (t : ℕ) (ht : t < free.length),
      x.mem (base + t) = (free.reverse[t]'(by simpa using ht)).val

/-! ## Section 3: Pure list helpers and core in-memory solver (`coreCode`) -/

private theorem argmin_append_singleton {α β : Type*} [LinearOrder β] (xs : List α) (x : α)
    (f : α → β) :
    (xs ++ [x]).argmin f =
      match xs.argmin f with
      | none => some x
      | some a => if f x < f a then some x else some a := by
  simp only [List.argmin, List.foldl_append, List.foldl_cons, List.foldl_nil, List.argAux]
  cases List.foldl (List.argAux fun a b => f a < f b) none xs <;> rfl

private theorem min?_append_singleton {β : Type*} [LinearOrder β] (xs : List β) (x : β) :
    (xs ++ [x]).min? =
      match xs.min? with
      | none => some x
      | some a => some (if x < a then x else a) := by
  cases h : xs.min? with
  | none =>
    rw [List.min?_eq_none_iff.mp h]
    simp
  | some a =>
    rw [List.min?_eq_some_iff] at h ⊢
    obtain ⟨ha_mem, ha_le⟩ := h
    split_ifs with hlt
    · refine ⟨List.mem_append_right _ (List.mem_singleton.mpr rfl), fun b hb => ?_⟩
      rcases List.mem_append.mp hb with hb | hb
      · exact (le_of_lt hlt).trans (ha_le b hb)
      · rw [List.mem_singleton.mp hb]
    · refine ⟨List.mem_append_left _ ha_mem, fun b hb => ?_⟩
      rcases List.mem_append.mp hb with hb | hb
      · exact ha_le b hb
      · rw [List.mem_singleton.mp hb]; exact le_of_not_gt hlt

private theorem bids_le_bids_auctionLoop {n : ℕ} (c : Fin n × Fin n → ℤ) (ε : ℤ) :
    ∀ (fuel : ℕ) (s : AuctionState n), s.bids ≤ (auctionLoop c ε fuel s).bids
  | 0, _ => le_rfl
  | fuel + 1, s => by
    rcases hs : s.free with _ | ⟨i, rest⟩
    · simp [auctionLoop, hs]
    · simp only [auctionLoop, hs]
      have h := bids_le_bids_auctionLoop c ε fuel (bidStep c ε s)
      rw [bids_bidStep hs] at h
      omega

private def initStackBody : Code .standard 26 := ram[
  val ← rn - one; val ← val - idx;
  addr ← bStack + idx; *addr ← val;
  idx ← idx + one ]

private def initCoreCode : Code .standard 26 :=
  .seq (Cslib.WordRAM.fillConst bOwner rn rn one idx addr)
    (.seq (Cslib.WordRAM.fillConst bPrice rn zero one idx addr)
      (.seq (ram[ idx ← #0 ])
        (.seq (.loop (.lt idx rn) initStackBody)
          (ram[ sp ← rn ]))))

private theorem exec_initCoreCode {w n matBase eps scale M : ℕ} (x : Data 26)
    (hb : BaseRegs n matBase eps scale M x)
    (hfit : Fits w (matBase + 2 * (n * n) + 3 * n)) :
    ∃ y, ExecWithin w initCoreCode x y (17 * n + 10) ∧
      BaseRegs n matBase eps scale M y ∧
      OwnerMem (matBase + 2 * (n * n)) (auctionInit n).owner y.mem ∧
      PriceMem (matBase + 2 * (n * n) + n) (auctionInit n).price y.mem ∧
      StackMem (matBase + 2 * (n * n) + 2 * n) (auctionInit n).free y ∧
      (∀ a, ¬(matBase + 2 * (n * n) ≤ a ∧ a < matBase + 2 * (n * n) + 3 * n) →
        y.mem a = x.mem a) := by
  obtain ⟨y₁, he₁_raw, hr₁_raw, _, hmem₁⟩ := Cslib.WordRAM.fillConst_exec (w := w)
    (base := bOwner) (len := rn) (val := rn) (one := one) (idx := idx) (addr := addr)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) hb.hone
    (by rw [hb.hbOwner, hb.hrn]; exact hfit.of_le (by omega))
    (by rw [hb.hrn]; exact hfit.of_le (by omega))
  have he₁ : ExecWithin w (Cslib.WordRAM.fillConst bOwner rn rn one idx addr) x y₁ (5 * n + 3) := by
    rw [hb.hrn] at he₁_raw; exact he₁_raw.within
  have hr₁ : ∀ i : Fin 26, i.val < 21 → y₁.regs i = x.regs i := fun i hi =>
    hr₁_raw i (fun h => by subst h; simp at hi) (fun h => by subst h; simp at hi)
  have hb₁ : BaseRegs n matBase eps scale M y₁ := hb.of_eq fun i hi => hr₁ i (by omega)
  obtain ⟨y₂, he₂_raw, hr₂_raw, _, hmem₂⟩ := Cslib.WordRAM.fillConst_exec (w := w) (x := y₁)
    (base := bPrice) (len := rn) (val := zero) (one := one) (idx := idx) (addr := addr)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) hb₁.hone
    (by rw [hb₁.hbPrice, hb₁.hrn]; exact hfit.of_le (by omega))
    (by rw [hb₁.hrn]; exact hfit.of_le (by omega))
  have he₂ :
      ExecWithin w (Cslib.WordRAM.fillConst bPrice rn zero one idx addr) y₁ y₂ (5 * n + 3) := by
    rw [hb₁.hrn] at he₂_raw; exact he₂_raw.within
  have hr₂ : ∀ i : Fin 26, i.val < 21 → y₂.regs i = y₁.regs i := fun i hi =>
    hr₂_raw i (fun h => by subst h; simp at hi) (fun h => by subst h; simp at hi)
  rw [hb₁.hbPrice, hb₁.hrn, hb₁.hzero] at hmem₂
  have hb₂ : BaseRegs n matBase eps scale M y₂ := hb₁.of_eq fun i hi => hr₂ i (by omega)
  have hs₀ : ∃ s₀, ExecWithin w (ram[ idx ← #0 ] : Code .standard 26) y₂ s₀ 1 ∧
      s₀ = y₂.set idx 0 := by
    refine WP.exists_execWithin ?_; wram_exec; rfl
  obtain ⟨s₀, he_s₀, rfl⟩ := hs₀
  let P (t : ℕ) (w_st : Data 26) : Prop :=
    t ≤ n ∧
      (∀ i : Fin 26, i.val < 14 → w_st.regs i = y₂.regs i) ∧
      (∀ k < t, w_st.mem (matBase + 2 * (n * n) + 2 * n + k) = n - 1 - k) ∧
      (∀ a, ¬(matBase + 2 * (n * n) + 2 * n ≤ a ∧ a < matBase + 2 * (n * n) + 2 * n + t) →
        w_st.mem a = y₂.mem a)
  have hP₀ : P 0 (y₂.set idx 0) :=
    ⟨Nat.zero_le _, fun i hi => by wram_simp, fun _ hk => absurd hk (Nat.not_lt_zero _),
      fun _ _ => rfl⟩
  have hbody (w_st : Data 26) (hw_st : P (w_st.regs idx) w_st) (hlt : w_st.regs idx < n) :
      ∃ z, ExecWithin w initStackBody w_st z 5 ∧ P (w_st.regs idx + 1) z ∧
        z.regs idx = w_st.regs idx + 1 := by
    obtain ⟨_, hr, hst, hf⟩ := hw_st
    have hbw : BaseRegs n matBase eps scale M w_st := hb₂.of_eq hr
    have h1_le_n : 1 ≤ n := by omega
    have hidx_le : w_st.regs idx ≤ n - 1 := by omega
    have hf_n1 : Fits w (n - 1) := hfit.of_le (by omega)
    have hf_sub : Fits w (n - 1 - w_st.regs idx) := hfit.of_le (by omega)
    have hf_addr : Fits w (matBase + 2 * (n * n) + 2 * n + w_st.regs idx) := hfit.of_le (by omega)
    have hf_idx1 : Fits w (w_st.regs idx + 1) := hfit.of_le (by omega)
    refine WP.exists_execWithin ?_
    unfold initStackBody
    wram_exec [hbw.hrn, hbw.hone, hbw.hbStack, h1_le_n, hidx_le, hf_n1, hf_sub, hf_addr, hf_idx1]
    refine ⟨⟨by omega, fun i hi => by wram_simp [hr i hi], fun k hk => ?_, fun a ha => ?_⟩,
      by wram_simp⟩
    · by_cases heq : k = w_st.regs idx
      · subst heq; wram_simp
      · wram_simp; exact hst k (by omega)
    · wram_simp; exact hf a (by omega)
  obtain ⟨y₃, hl_st, hPn, _⟩ := ExecWithin.loop_count P
    (fun w_st hw_st => (hw_st.2.1 rn (by decide)).trans hb₂.hrn) hbody
    (x := y₂.set idx 0) (by simp) (by simpa using hP₀)
  obtain ⟨_, hr₃, hst₃, hf₃⟩ := hPn
  have hb₃ : BaseRegs n matBase eps scale M y₃ := hb₂.of_eq hr₃
  have hsp_step : ∃ y, ExecWithin w (ram[ sp ← rn ] : Code .standard 26) y₃ y 1 ∧
      y = y₃.set sp n := by
    refine WP.exists_execWithin ?_; wram_exec [hb₃.hrn]; rfl
  obtain ⟨y, he_sp, rfl⟩ := hsp_step
  let y := y₃.set sp n
  have hby : BaseRegs n matBase eps scale M y := hb₃.of_eq fun i hi => by dsimp only [y]; wram_simp
  have hown : OwnerMem (matBase + 2 * (n * n)) (auctionInit n).owner y.mem := fun j => by
    dsimp only [y, Data.set]
    rw [hf₃ _ (by have := j.isLt; omega), hmem₂,
      fill_of_not_owns (by simp only [Block.Owns]; have := j.isLt; omega),
      hmem₁, hb.hbOwner, hb.hrn]
    simpa [auctionInit, encodeOptFin] using
      fill_of_owns ⟨Nat.le_add_right _ _, Nat.add_lt_add_left j.isLt _⟩
  have hprc : PriceMem (matBase + 2 * (n * n) + n) (auctionInit n).price y.mem := fun j => by
    dsimp only [y, Data.set]
    rw [hf₃ _ (by have := j.isLt; omega), hmem₂]
    simpa [auctionInit] using fill_of_owns ⟨Nat.le_add_right _ _, Nat.add_lt_add_left j.isLt _⟩
  have hstk : StackMem (matBase + 2 * (n * n) + 2 * n) (auctionInit n).free y := by
    refine ⟨by dsimp only [y]; wram_simp; simp [auctionInit], fun t ht => ?_⟩
    have ht_lt : t < n := by simpa [auctionInit] using ht
    dsimp only [y, Data.set]
    rw [hst₃ t ht_lt]
    simp [auctionInit, List.getElem_reverse]
  have hout_frame : ∀ a, ¬(matBase + 2 * (n * n) ≤ a ∧ a < matBase + 2 * (n * n) + 3 * n) →
      y.mem a = x.mem a := fun a ha => by
    dsimp only [y, Data.set]
    rw [hf₃ a (by omega), hmem₂, fill_of_not_owns (by simp only [Block.Owns]; omega),
      hmem₁, hb.hbOwner, hb.hrn]
    exact fill_of_not_owns (by simp only [Block.Owns]; omega)
  refine ⟨y, (he₁.seq (he₂.seq (he_s₀.seq (hl_st.seq he_sp)))).mono (by simp; omega),
    hby, hown, hprc, hstk, hout_frame⟩

private def findBestBody : Code .standard 26 := ram[
  addr ← rowBase + idx; val ← *addr;
  addr ← bPrice + idx; val2 ← *addr;
  val ← val + val2;
  if idx = zero then [
    bestJ ← idx; bestVal ← val
  ] else [
    if val < bestVal then [ bestJ ← idx; bestVal ← val ] else [ tmp ← zero ]
  ];
  idx ← idx + one ]

private def findBestCode : Code .standard 26 :=
  .seq (ram[ idx ← #0 ]) (.loop (.lt idx rn) findBestBody)

private def findSecondBody : Code .standard 26 := ram[
  if idx = bestJ then [ tmp ← zero ] else [
    addr ← rowBase + idx; val ← *addr;
    addr ← bPrice + idx; val2 ← *addr;
    val ← val + val2;
    if hasSecond = zero then [
      hasSecond ← one; secondVal ← val
    ] else [
      if val < secondVal then [ secondVal ← val ] else [ tmp ← zero ]
    ]
  ];
  idx ← idx + one ]

private def findSecondCode : Code .standard 26 :=
  .seq (ram[ hasSecond ← #0; secondVal ← #0; idx ← #0 ])
    (.loop (.lt idx rn) findSecondBody)

private def applyBidTail : Code .standard 26 :=
  .seq (ram[
    if hasSecond = zero then [
      addr ← bPrice + bestJ; val ← *addr;
      val ← val + reps
    ] else [
      addr ← rowBase + bestJ; val2 ← *addr;
      val ← secondVal - val2;
      val ← val + reps
    ] ])
    (.seq (ram[ addr ← bPrice + bestJ; *addr ← val;
                addr ← bOwner + bestJ; val2 ← *addr;
                *addr ← curI ])
      (ram[ if val2 < rn then [
              addr ← bStack + sp; *addr ← val2;
              sp ← sp + one
            ] else [ tmp ← zero ] ]))

private def bidStepCode : Code .standard 26 :=
  .seq (ram[ sp ← sp - one; addr ← bStack + sp; curI ← *addr;
             rowBase ← curI * rn; rowBase ← bC + rowBase ])
    (.seq findBestCode (.seq findSecondCode applyBidTail))

/-- Structured word-RAM implementation of `auction` on an in-memory unsigned `n × n` cost matrix
at `bC` with bidding increment `reps`. -/
def coreCode : Code .standard 26 :=
  .seq initCoreCode (.loop (.lt zero sp) bidStepCode)

private theorem exec_findBestCode {w n matBase eps scale M W : ℕ}
    {C : Fin n × Fin n → ℕ} (hC : ∀ i j, C (i, j) ≤ W)
    {price : Fin n → ℤ} (hp_nonneg : ∀ k, 0 ≤ price k) (hp_le : ∀ k, price k ≤ (W + eps : ℤ))
    (i₀ : Fin n) (x : Data 26) (hb : BaseRegs n matBase eps scale M x)
    (hCM : CostMem (matBase + n * n) C x.mem)
    (hPM : PriceMem (matBase + 2 * (n * n) + n) price x.mem)
    (hrb : x.regs rowBase = matBase + n * n + i₀.val * n)
    (hfit : Fits w (matBase + 2 * (n * n) + 4 * n + 2 * W + 2 * eps + 4)) :
    let cZ : Fin n × Fin n → ℤ := fun e => (C e : ℤ)
    ∃ y j₀, ExecWithin w findBestCode x y (13 * n + 3) ∧
      bestObject cZ price i₀ = some j₀ ∧
      (∀ k : Fin n, redCost cZ price i₀ j₀ ≤ redCost cZ price i₀ k) ∧
      (∀ r : Fin 26, r.val < 17 → y.regs r = x.regs r) ∧
      y.regs bestJ = j₀.val ∧
      (y.regs bestVal : ℤ) = redCost cZ price i₀ j₀ ∧
      y.mem = x.mem := by
  intro cZ
  have hn_pos : 0 < n := Nat.zero_lt_of_lt i₀.isLt
  have hs₀ : ∃ s₀, ExecWithin w (ram[ idx ← #0 ] : Code .standard 26) x s₀ 1 ∧
      s₀ = x.set idx 0 := by
    refine WP.exists_execWithin ?_; wram_exec; rfl
  obtain ⟨s₀, he₀, rfl⟩ := hs₀
  let rcNat (k : Fin n) : ℕ := C (i₀, k) + (price k).toNat
  have hrc_eq : ∀ k : Fin n, (rcNat k : ℤ) = redCost cZ price i₀ k := fun k => by
    have := hp_nonneg k
    simp only [rcNat, redCost, cZ]
    omega
  have hrc_le : ∀ k : Fin n, rcNat k ≤ 2 * W + eps := fun k => by
    have := hC i₀ k
    have := hp_nonneg k
    have := hp_le k
    dsimp only [rcNat]
    omega
  let PB (t : ℕ) (y : Data 26) : Prop :=
    t ≤ n ∧
      (∀ r : Fin 26, r.val < 17 → y.regs r = x.regs r) ∧
      y.mem = x.mem ∧
      (0 < t → ∃ j_t : Fin n,
        (((List.finRange n).take t).argmin (redCost cZ price i₀)) = some j_t ∧
          y.regs bestJ = j_t.val ∧ y.regs bestVal = rcNat j_t)
  have hPB₀ : PB 0 (x.set idx 0) :=
    ⟨Nat.zero_le _, fun r hr => by wram_simp, rfl, fun h => absurd h (Nat.lt_irrefl 0)⟩
  have hbody (y : Data 26) (hy : PB (y.regs idx) y) (hlt : y.regs idx < n) :
      ∃ z, ExecWithin w findBestBody y z 11 ∧ PB (y.regs idx + 1) z ∧
        z.regs idx = y.regs idx + 1 := by
    obtain ⟨_, hr, hmem, hinv⟩ := hy
    have hby : BaseRegs n matBase eps scale M y := hb.of_eq fun r hr' => hr r (by omega)
    have hy_rb : y.regs rowBase = matBase + n * n + i₀.val * n :=
      (hr rowBase (by decide)).trans hrb
    let k₀ : Fin n := ⟨y.regs idx, hlt⟩
    have hmul_lt : i₀.val * n + y.regs idx < n * n := Cslib.Matrix.pairIndex_lt (i₀, k₀)
    have hC_k : y.mem (matBase + n * n + i₀.val * n + y.regs idx) = C (i₀, k₀) := by
      rw [hmem, Nat.add_assoc (matBase + n * n)]
      exact hCM.hentry i₀ k₀
    have hP_k : y.mem (matBase + 2 * (n * n) + n + y.regs idx) = (price k₀).toNat := by
      rw [hmem]
      exact hPM k₀
    have hf_c : Fits w (matBase + n * n + i₀.val * n + y.regs idx) := hfit.of_le (by omega)
    have hf_p : Fits w (matBase + 2 * (n * n) + n + y.regs idx) := hfit.of_le (by omega)
    have hf_rc : Fits w (rcNat k₀) := by
      have := hrc_le k₀; exact hfit.of_le (by omega)
    have hf_idx1 : Fits w (y.regs idx + 1) := hfit.of_le (by omega)
    have htake_succ : (List.finRange n).take (y.regs idx + 1) =
        (List.finRange n).take (y.regs idx) ++ [k₀] := List.take_succ_finRange hlt
    refine WP.exists_execWithin ?_
    unfold findBestBody
    by_cases ht0 : y.regs idx = 0
    · have hc0 : y.regs zero = y.regs idx := hby.hzero.trans ht0.symm
      wram_exec [hy_rb, hby.hbPrice, hby.hone, hc0, hC_k, hP_k,
        hf_c, hf_p, hf_rc, hf_idx1]
      refine ⟨⟨by omega, fun r hr' => by wram_simp [hr r hr'], hmem, fun _ => ?_⟩, by wram_simp⟩
      refine ⟨k₀, ?_, by wram_simp [k₀], by wram_simp; rfl⟩
      rw [htake_succ, ht0, List.take_zero, List.nil_append]
      rfl
    · obtain ⟨j_t, harg_t, hbj_t, hbv_t⟩ := hinv (Nat.pos_of_ne_zero ht0)
      have hc0 : y.regs idx ≠ y.regs zero := by rw [hby.hzero]; exact ht0
      by_cases hlt_rc : rcNat k₀ < rcNat j_t
      · have hlt_z : redCost cZ price i₀ k₀ < redCost cZ price i₀ j_t := by
          rw [← hrc_eq k₀, ← hrc_eq j_t]; exact Nat.cast_lt.mpr hlt_rc
        wram_exec [hy_rb, hby.hbPrice, hby.hone, hc0, hC_k, hP_k, hbv_t, hlt_rc,
          hf_c, hf_p, hf_rc, hf_idx1]
        refine ⟨⟨by omega, fun r hr' => by wram_simp [hr r hr'], hmem, fun _ => ?_⟩, by wram_simp⟩
        refine ⟨k₀, ?_, by wram_simp [k₀], by wram_simp; rfl⟩
        rw [htake_succ, argmin_append_singleton, harg_t]
        dsimp only
        exact ite_eq_left hlt_z
      · have hge_z : ¬redCost cZ price i₀ k₀ < redCost cZ price i₀ j_t := by
          rw [← hrc_eq k₀, ← hrc_eq j_t]; exact mod_cast hlt_rc
        wram_exec [hy_rb, hby.hbPrice, hby.hone, hc0, hC_k, hP_k, hbv_t, hlt_rc,
          hf_c, hf_p, hf_rc, hf_idx1]
        refine ⟨⟨by omega, fun r hr' => by wram_simp [hr r hr'], hmem, fun _ => ?_⟩, by wram_simp⟩
        refine ⟨j_t, ?_, by wram_simp [hbj_t], by wram_simp [hbv_t]⟩
        rw [htake_succ, argmin_append_singleton, harg_t]
        dsimp only
        exact ite_eq_right hge_z
  obtain ⟨y, hl, hPBn, _⟩ := ExecWithin.loop_count PB
    (fun w_st hw_st => (hw_st.2.1 rn (by decide)).trans hb.hrn) hbody
    (x := x.set idx 0) (by simp) (by simpa using hPB₀)
  obtain ⟨_, hr_y, hmem_y, hinv_y⟩ := hPBn
  obtain ⟨j₀, harg_n, hbj_y, hbv_y⟩ := hinv_y hn_pos
  rw [List.take_of_length_le (by simp)] at harg_n
  have hbo : bestObject cZ price i₀ = some j₀ := harg_n
  exact ⟨y, j₀, (he₀.seq hl).mono (by simp; omega), hbo,
    fun k => List.le_of_mem_argmin (List.mem_finRange k) hbo,
    hr_y, hbj_y, by rw [hbv_y, hrc_eq], hmem_y⟩

private theorem exec_findSecondCode {w n matBase eps scale M W : ℕ}
    {C : Fin n × Fin n → ℕ} (hC : ∀ i j, C (i, j) ≤ W)
    {price : Fin n → ℤ} (hp_nonneg : ∀ k, 0 ≤ price k) (hp_le : ∀ k, price k ≤ (W + eps : ℤ))
    (i₀ j₀ : Fin n) (x : Data 26) (hb : BaseRegs n matBase eps scale M x)
    (hCM : CostMem (matBase + n * n) C x.mem)
    (hPM : PriceMem (matBase + 2 * (n * n) + n) price x.mem)
    (hrb : x.regs rowBase = matBase + n * n + i₀.val * n)
    (hbj : x.regs bestJ = j₀.val)
    (hfit : Fits w (matBase + 2 * (n * n) + 4 * n + 2 * W + 2 * eps + 4)) :
    let cZ : Fin n × Fin n → ℤ := fun e => (C e : ℤ)
    ∃ y, ExecWithin w findSecondCode x y (15 * n + 5) ∧
      (∀ r : Fin 26, r.val < 19 → y.regs r = x.regs r) ∧
      y.mem = x.mem ∧
      match secondBest cZ price i₀ j₀ with
      | none => y.regs hasSecond = 0
      | some wVal =>
        y.regs hasSecond = 1 ∧ (y.regs secondVal : ℤ) = wVal ∧ y.regs secondVal ≤ 2 * W + eps := by
  intro cZ
  have hs₀ : ∃ s₀, ExecWithin w
      (ram[ hasSecond ← #0; secondVal ← #0; idx ← #0 ] : Code .standard 26) x s₀ 3 ∧
      s₀ = ((x.set hasSecond 0).set secondVal 0).set idx 0 := by
    refine WP.exists_execWithin ?_; wram_exec; rfl
  obtain ⟨s₀, he₀, rfl⟩ := hs₀
  let rcNat (k : Fin n) : ℕ := C (i₀, k) + (price k).toNat
  have hrc_eq : ∀ k : Fin n, (rcNat k : ℤ) = redCost cZ price i₀ k := fun k => by
    have := hp_nonneg k; simp only [rcNat, redCost, cZ]; omega
  have hrc_le : ∀ k : Fin n, rcNat k ≤ 2 * W + eps := fun k => by
    have := hC i₀ k; have := hp_nonneg k; have := hp_le k; dsimp only [rcNat]; omega
  let cand (t : ℕ) : List ℤ :=
    (((List.finRange n).take t).filter fun k => decide (k ≠ j₀)).map (redCost cZ price i₀)
  let PS (t : ℕ) (y : Data 26) : Prop :=
    t ≤ n ∧
      (∀ r : Fin 26, r.val < 19 → y.regs r = x.regs r) ∧
      y.mem = x.mem ∧
      match (cand t).min? with
      | none => y.regs hasSecond = 0
      | some wVal =>
        y.regs hasSecond = 1 ∧ (y.regs secondVal : ℤ) = wVal ∧ y.regs secondVal ≤ 2 * W + eps
  have hPS₀ : PS 0 (((x.set hasSecond 0).set secondVal 0).set idx 0) :=
    ⟨Nat.zero_le _, fun r hr => by wram_simp, rfl, by simp [cand]⟩
  have hbody (y : Data 26) (hy : PS (y.regs idx) y) (hlt : y.regs idx < n) :
      ∃ z, ExecWithin w findSecondBody y z 13 ∧ PS (y.regs idx + 1) z ∧
        z.regs idx = y.regs idx + 1 := by
    obtain ⟨_, hr, hmem, hinv⟩ := hy
    have hby : BaseRegs n matBase eps scale M y := hb.of_eq fun r hr' => hr r (by omega)
    have hy_rb : y.regs rowBase = matBase + n * n + i₀.val * n :=
      (hr rowBase (by decide)).trans hrb
    have hy_bj : y.regs bestJ = j₀.val := (hr bestJ (by decide)).trans hbj
    let k₀ : Fin n := ⟨y.regs idx, hlt⟩
    have hf_idx1 : Fits w (y.regs idx + 1) := hfit.of_le (by omega)
    refine WP.exists_execWithin ?_
    unfold findSecondBody
    by_cases hkj : y.regs idx = j₀.val
    · have hk_eq_j : (⟨y.regs idx, hlt⟩ : Fin n) = j₀ := Fin.ext hkj
      have hcand_eq : cand (y.regs idx + 1) = cand (y.regs idx) := by
        simp [cand, List.take_succ_finRange hlt, hk_eq_j]
      have hcond : y.regs bestJ = y.regs idx := hy_bj.trans hkj.symm
      wram_exec [hby.hzero, hby.hone, hcond, hf_idx1]
      refine ⟨⟨by omega, fun r hr' => by wram_simp [hr r hr'], hmem, ?_⟩, by wram_simp⟩
      rw [hcand_eq]
      cases hmin : (cand (y.regs idx)).min? with
      | none => rw [hmin] at hinv; wram_simp [hinv]
      | some wVal => rw [hmin] at hinv; exact ⟨by wram_simp [hinv.1], hinv.2.1, hinv.2.2⟩
    · have hk_ne_j : k₀ ≠ j₀ := fun h => hkj (congrArg Fin.val h)
      have hcand_eq : cand (y.regs idx + 1) = cand (y.regs idx) ++ [redCost cZ price i₀ k₀] := by
        simp [cand, List.take_succ_finRange hlt, hk_ne_j, k₀]
      have hcond : y.regs idx ≠ y.regs bestJ := by rw [hy_bj]; exact hkj
      have hmul_lt : i₀.val * n + y.regs idx < n * n := Cslib.Matrix.pairIndex_lt (i₀, k₀)
      have hC_k : y.mem (matBase + n * n + i₀.val * n + y.regs idx) = C (i₀, k₀) := by
        rw [hmem, Nat.add_assoc (matBase + n * n)]; exact hCM.hentry i₀ k₀
      have hP_k : y.mem (matBase + 2 * (n * n) + n + y.regs idx) = (price k₀).toNat := by
        rw [hmem]; exact hPM k₀
      have hf_c : Fits w (matBase + n * n + i₀.val * n + y.regs idx) := hfit.of_le (by omega)
      have hf_p : Fits w (matBase + 2 * (n * n) + n + y.regs idx) := hfit.of_le (by omega)
      have hf_rc : Fits w (rcNat k₀) := by
        have := hrc_le k₀; exact hfit.of_le (by omega)
      cases hmin : (cand (y.regs idx)).min? with
      | none =>
        rw [hmin] at hinv
        have hhs0 : y.regs hasSecond = y.regs zero := hinv.trans hby.hzero.symm
        wram_exec [hy_rb, hby.hbPrice, hby.hone, hcond, hC_k, hP_k, hhs0,
          hf_c, hf_p, hf_rc, hf_idx1]
        refine ⟨⟨by omega, fun r hr' => by wram_simp [hr r hr'], hmem, ?_⟩, by wram_simp⟩
        rw [hcand_eq, min?_append_singleton, hmin]
        exact ⟨by wram_simp, by wram_simp; exact hrc_eq k₀, by wram_simp; exact hrc_le k₀⟩
      | some wVal =>
        rw [hmin] at hinv
        obtain ⟨hhs1, hsv_eq, hsv_le⟩ := hinv
        have hhs_ne0 : y.regs hasSecond ≠ y.regs zero := by rw [hby.hzero]; omega
        by_cases hlt_sv : rcNat k₀ < y.regs secondVal
        · have hlt_z : redCost cZ price i₀ k₀ < wVal := by
            rw [← hrc_eq k₀, ← hsv_eq]; exact Nat.cast_lt.mpr hlt_sv
          wram_exec [hy_rb, hby.hbPrice, hby.hone, hcond, hC_k, hP_k,
            hhs_ne0, hlt_sv, hf_c, hf_p, hf_rc, hf_idx1]
          refine ⟨⟨by omega, fun r hr' => by wram_simp [hr r hr'], hmem, ?_⟩, by wram_simp⟩
          rw [hcand_eq, min?_append_singleton, hmin]
          dsimp only
          rw [ite_eq_left hlt_z]
          exact ⟨by wram_simp [hhs1], by wram_simp; exact hrc_eq k₀,
            by wram_simp; exact hrc_le k₀⟩
        · have hge_z : ¬redCost cZ price i₀ k₀ < wVal := by
            rw [← hrc_eq k₀, ← hsv_eq]; exact mod_cast hlt_sv
          wram_exec [hy_rb, hby.hbPrice, hby.hzero, hby.hone, hcond, hC_k, hP_k,
            hhs_ne0, hlt_sv, hf_c, hf_p, hf_rc, hf_idx1]
          refine ⟨⟨by omega, fun r hr' => by wram_simp [hr r hr'], hmem, ?_⟩, by wram_simp⟩
          rw [hcand_eq, min?_append_singleton, hmin]
          dsimp only
          rw [ite_eq_right hge_z]
          exact ⟨by wram_simp [hhs1], by wram_simp [hsv_eq], by wram_simp; exact hsv_le⟩
  obtain ⟨y, hl, hPSn, _⟩ := ExecWithin.loop_count PS
    (fun w_st hw_st => (hw_st.2.1 rn (by decide)).trans hb.hrn) hbody
    (x := ((x.set hasSecond 0).set secondVal 0).set idx 0) (by simp) (by simpa using hPS₀)
  obtain ⟨_, hr_y, hmem_y, hinv_y⟩ := hPSn
  have hcand_full : cand n =
      (((List.finRange n).filter fun k => decide (k ≠ j₀)).map (redCost cZ price i₀)) := by
    simp only [cand, List.take_of_length_le (by simp : (List.finRange n).length ≤ n)]
  rw [hcand_full] at hinv_y
  exact ⟨y, (he₀.seq hl).mono (by simp; omega), hr_y, hmem_y, hinv_y⟩

private theorem exec_bidStepCode {w n matBase eps scale M W : ℕ}
    {C : Fin n × Fin n → ℕ} (hC : ∀ i j, C (i, j) ≤ W)
    {s : AuctionState n} {i₀ : Fin n} {rest : List (Fin n)} (hs : s.free = i₀ :: rest)
    (hinv : AuctionInv (fun e => (C e : ℤ)) (eps : ℤ) s)
    (hp_nonneg : ∀ k, 0 ≤ s.price k)
    (x : Data 26) (hb : BaseRegs n matBase eps scale M x)
    (hCM : CostMem (matBase + n * n) C x.mem)
    (hOM : OwnerMem (matBase + 2 * (n * n)) s.owner x.mem)
    (hPM : PriceMem (matBase + 2 * (n * n) + n) s.price x.mem)
    (hSM : StackMem (matBase + 2 * (n * n) + 2 * n) s.free x)
    (hfit : Fits w (matBase + 2 * (n * n) + 4 * n + 2 * W + 2 * eps + 4)) :
    let cZ : Fin n × Fin n → ℤ := fun e => (C e : ℤ)
    let s' := bidStep cZ (eps : ℤ) s
    ∃ y, ExecWithin w bidStepCode x y (28 * n + 28) ∧
      BaseRegs n matBase eps scale M y ∧
      OwnerMem (matBase + 2 * (n * n)) s'.owner y.mem ∧
      PriceMem (matBase + 2 * (n * n) + n) s'.price y.mem ∧
      StackMem (matBase + 2 * (n * n) + 2 * n) s'.free y ∧
      (∀ a, ¬(matBase + 2 * (n * n) ≤ a ∧ a < matBase + 2 * (n * n) + 3 * n) →
        y.mem a = x.mem a) := by
  intro cZ s'
  have hi₀_lt := i₀.isLt
  have hnd := hinv.free_nodup
  have hlen_le_n : s.free.length ≤ n := by simpa using hnd.length_le_card
  have hrest_lt_n : rest.length < n := by rw [hs, List.length_cons] at hlen_le_n; omega
  have hp_le : ∀ k : Fin n, s.price k ≤ (W + eps : ℤ) :=
    hinv.price_le (by simp [hs])
      (fun i j k => by have := hC i k; omega) (Nat.cast_nonneg eps)
  have hsp_x : x.regs sp = rest.length + 1 := by rw [hSM.1, hs, List.length_cons]
  have htop_mem : x.mem (matBase + 2 * (n * n) + 2 * n + rest.length) = i₀.val := by
    have ht : rest.length < s.free.length := by rw [hs, List.length_cons]; omega
    have hget := hSM.2 rest.length ht
    rw [hget]
    simp only [hs, List.reverse_cons]
    have hlen_rev : rest.reverse.length = rest.length := List.length_reverse
    rw [List.getElem_append_right (by omega)]
    simp [hlen_rev]
  have hf_sp : Fits w rest.length := hfit.of_le (by omega)
  have hf_st_addr : Fits w (matBase + 2 * (n * n) + 2 * n + rest.length) := hfit.of_le (by omega)
  have hf_mul : Fits w (i₀.val * n) := by
    have : i₀.val * n < n * n := Nat.mul_lt_mul_of_pos_right hi₀_lt (Nat.zero_lt_of_lt hi₀_lt)
    exact hfit.of_le (by omega)
  have hf_rb : Fits w (matBase + n * n + i₀.val * n) := by
    have : i₀.val * n < n * n := Nat.mul_lt_mul_of_pos_right hi₀_lt (Nat.zero_lt_of_lt hi₀_lt)
    exact hfit.of_le (by omega)
  have hpop : ∃ y₁, ExecWithin w
      (ram[ sp ← sp - one; addr ← bStack + sp; curI ← *addr;
            rowBase ← curI * rn; rowBase ← bC + rowBase ] : Code .standard 26) x y₁ 5 ∧
      (∀ r : Fin 26, r.val < 14 → y₁.regs r = x.regs r) ∧
      y₁.regs sp = rest.length ∧ y₁.regs curI = i₀.val ∧
      y₁.regs rowBase = matBase + n * n + i₀.val * n ∧ y₁.mem = x.mem := by
    refine WP.exists_execWithin ?_
    wram_exec [hsp_x, hb.hone, hb.hbStack, hb.hrn, hb.hbC, htop_mem,
      hf_sp, hf_st_addr, hf_mul, hf_rb]
    exact ⟨fun r hr => by wram_simp, by wram_simp, by wram_simp, by wram_simp, rfl⟩
  obtain ⟨y₁, he_pop, hr₁, hsp₁, hci₁, hrb₁, hmem₁⟩ := hpop
  have hb₁ : BaseRegs n matBase eps scale M y₁ := hb.of_eq hr₁
  have hCM₁ : CostMem (matBase + n * n) C y₁.mem := hmem₁ ▸ hCM
  have hPM₁ : PriceMem (matBase + 2 * (n * n) + n) s.price y₁.mem := hmem₁ ▸ hPM
  obtain ⟨y₂, j₀, he_best, hbo, hj₀_min, hr₂, hbj₂, hbv₂, hmem₂⟩ :=
    exec_findBestCode hC hp_nonneg hp_le i₀ y₁ hb₁ hCM₁ hPM₁ hrb₁ hfit
  have hb₂ : BaseRegs n matBase eps scale M y₂ := hb₁.of_eq fun r hr => hr₂ r (by omega)
  have hCM₂ : CostMem (matBase + n * n) C y₂.mem := hmem₂ ▸ hCM₁
  have hPM₂ : PriceMem (matBase + 2 * (n * n) + n) s.price y₂.mem := hmem₂ ▸ hPM₁
  have hrb₂ : y₂.regs rowBase = matBase + n * n + i₀.val * n :=
    (hr₂ rowBase (by decide)).trans hrb₁
  obtain ⟨y₃, he_sec, hr₃, hmem₃, hsec₃⟩ :=
    exec_findSecondCode hC hp_nonneg hp_le i₀ j₀ y₂ hb₂ hCM₂ hPM₂ hrb₂ hbj₂ hfit
  have hb₃ : BaseRegs n matBase eps scale M y₃ := hb₂.of_eq fun r hr => hr₃ r (by omega)
  have hsp₃ : y₃.regs sp = rest.length :=
    (hr₃ sp (by decide)).trans ((hr₂ sp (by decide)).trans hsp₁)
  have hci₃ : y₃.regs curI = i₀.val :=
    (hr₃ curI (by decide)).trans ((hr₂ curI (by decide)).trans hci₁)
  have hrb₃ : y₃.regs rowBase = matBase + n * n + i₀.val * n :=
    (hr₃ rowBase (by decide)).trans hrb₂
  have hbj₃ : y₃.regs bestJ = j₀.val := (hr₃ bestJ (by decide)).trans hbj₂
  have hbv₃ : (y₃.regs bestVal : ℤ) = redCost cZ s.price i₀ j₀ :=
    (congrArg Nat.cast (hr₃ bestVal (by decide))).trans hbv₂
  have hmem₃_x : y₃.mem = x.mem := hmem₃.trans (hmem₂.trans hmem₁)
  have hs'_eq : s' =
      { owner := Function.update s.owner j₀ (some i₀)
        price := Function.update s.price j₀ (bidPrice cZ (eps : ℤ) s.price i₀ j₀)
        free := (s.owner j₀).toList ++ rest
        bids := s.bids + 1 } := by
    simp only [s', bidStep, hs, cZ, hbo]
  have hj₀_lt := j₀.isLt
  have hmul_ij : i₀.val * n + j₀.val < n * n := Cslib.Matrix.pairIndex_lt (i₀, j₀)
  have hf_pj : Fits w (matBase + 2 * (n * n) + n + j₀.val) := hfit.of_le (by omega)
  have hf_oj : Fits w (matBase + 2 * (n * n) + j₀.val) := hfit.of_le (by omega)
  have hf_cj : Fits w (matBase + n * n + i₀.val * n + j₀.val) := hfit.of_le (by omega)
  let newP : ℕ := (bidPrice cZ (eps : ℤ) s.price i₀ j₀).toNat
  have hnewP_nonneg : 0 ≤ bidPrice cZ (eps : ℤ) s.price i₀ j₀ := by
    have hle := le_bidPrice (c := cZ) (ε := (eps : ℤ)) hj₀_min
    have := hp_nonneg j₀
    omega
  -- Execute the price computation prefix of `applyBidTail`
  have hprice_part : ∃ y₄, ExecWithin w
      (ram[ if hasSecond = zero then [
              addr ← bPrice + bestJ; val ← *addr;
              val ← val + reps
            ] else [
              addr ← rowBase + bestJ; val2 ← *addr;
              val ← secondVal - val2;
              val ← val + reps
            ] ] : Code .standard 26) y₃ y₄ 6 ∧
      (∀ r : Fin 26, r.val < 21 → y₄.regs r = y₃.regs r) ∧
      y₄.regs val = newP ∧ y₄.mem = x.mem := by
    refine WP.exists_execWithin ?_
    cases hsb : secondBest cZ s.price i₀ j₀ with
    | none =>
      rw [hsb] at hsec₃
      have hPj : y₃.mem (matBase + 2 * (n * n) + n + j₀.val) = (s.price j₀).toNat := by
        rw [hmem₃_x]; exact hPM j₀
      have hval_eq : (s.price j₀).toNat + eps = newP := by
        have := hp_nonneg j₀
        dsimp only [newP, bidPrice]
        rw [hsb]
        dsimp only
        omega
      have hpj_le := hp_le j₀
      have hpj_nn := hp_nonneg j₀
      have hf_np : Fits w ((s.price j₀).toNat + eps) := hfit.of_le (by omega)
      wram_exec [hsec₃, hb₃.hzero, hb₃.hbPrice, hbj₃, hb₃.hreps, hPj, hf_pj, hf_np]
      exact ⟨fun r hr => by wram_simp, by wram_simp [hval_eq], hmem₃_x⟩
    | some wVal =>
      rw [hsb] at hsec₃
      obtain ⟨hhs1, hsv_z, hsv_le⟩ := hsec₃
      have hhs_ne0 : y₃.regs hasSecond ≠ 0 := by omega
      have hCj : y₃.mem (matBase + n * n + i₀.val * n + j₀.val) = C (i₀, j₀) := by
        rw [hmem₃_x, Nat.add_assoc (matBase + n * n)]; exact hCM.hentry i₀ j₀
      have hw_ge_rc : redCost cZ s.price i₀ j₀ ≤ wVal := by
        rw [secondBest, List.min?_eq_some_iff] at hsb
        obtain ⟨hmem_w, _⟩ := hsb
        obtain ⟨k_w, _, rfl⟩ := List.mem_map.mp hmem_w
        exact hj₀_min k_w
      have hCj_le_sv : C (i₀, j₀) ≤ y₃.regs secondVal := by
        have hpj_nn := hp_nonneg j₀
        simp only [redCost, cZ] at hw_ge_rc
        omega
      have hval_eq : y₃.regs secondVal - C (i₀, j₀) + eps = newP := by
        dsimp only [newP, bidPrice, cZ]
        rw [hsb]
        dsimp only
        omega
      have hf_sub : Fits w (y₃.regs secondVal - C (i₀, j₀)) := hfit.of_le (by omega)
      have hf_np : Fits w (y₃.regs secondVal - C (i₀, j₀) + eps) := hfit.of_le (by omega)
      wram_exec [hhs_ne0, hb₃.hzero, hrb₃, hbj₃, hb₃.hreps, hCj, hCj_le_sv,
        hf_cj, hf_sub, hf_np]
      exact ⟨fun r hr => by wram_simp, by wram_simp [hval_eq], hmem₃_x⟩
  obtain ⟨y₄, he_p, hr₄, hval₄, hmem₄⟩ := hprice_part
  have hb₄ : BaseRegs n matBase eps scale M y₄ := hb₃.of_eq fun r hr => hr₄ r (by omega)
  have hsp₄ : y₄.regs sp = rest.length := (hr₄ sp (by decide)).trans hsp₃
  have hci₄ : y₄.regs curI = i₀.val := (hr₄ curI (by decide)).trans hci₃
  have hbj₄ : y₄.regs bestJ = j₀.val := (hr₄ bestJ (by decide)).trans hbj₃
  have hOj : y₄.mem (matBase + 2 * (n * n) + j₀.val) = encodeOptFin (s.owner j₀) := by
    rw [hmem₄]; exact hOM j₀
  have hupd_part : ∃ y₅, ExecWithin w
      (ram[ addr ← bPrice + bestJ; *addr ← val;
            addr ← bOwner + bestJ; val2 ← *addr;
            *addr ← curI ] : Code .standard 26) y₄ y₅ 5 ∧
      BaseRegs n matBase eps scale M y₅ ∧
      y₅.regs sp = rest.length ∧
      y₅.regs val2 = encodeOptFin (s.owner j₀) ∧
      OwnerMem (matBase + 2 * (n * n)) s'.owner y₅.mem ∧
      PriceMem (matBase + 2 * (n * n) + n) s'.price y₅.mem ∧
      (∀ a, ¬(matBase + 2 * (n * n) ≤ a ∧ a < matBase + 2 * (n * n) + 2 * n) →
        y₅.mem a = x.mem a) := by
    refine WP.exists_execWithin ?_
    wram_exec [hb₄.hbPrice, hb₄.hbOwner, hbj₄, hval₄, hci₄, hOj, hf_pj, hf_oj]
    refine ⟨hb₄.of_eq fun r hr => by wram_simp, by wram_simp [hsp₄], by wram_simp,
      fun j => ?_, fun j => ?_, fun a ha => by wram_simp [hmem₄]⟩
    · rw [hs'_eq]; dsimp only
      by_cases hjj : j = j₀
      · subst hjj; rw [Function.update_self]; wram_simp [encodeOptFin]
      · have : j.val ≠ j₀.val := fun h => hjj (Fin.ext h)
        rw [Function.update_of_ne hjj]; wram_simp [hmem₄, hOM j]
    · rw [hs'_eq]; dsimp only
      by_cases hjj : j = j₀
      · subst hjj; rw [Function.update_self]; wram_simp [newP]
      · have : j.val ≠ j₀.val := fun h => hjj (Fin.ext h)
        rw [Function.update_of_ne hjj]; wram_simp [hmem₄, hPM j]
  obtain ⟨y₅, he_upd, hb₅, hsp₅, hv2₅, hOy₅, hPy₅, hf₅⟩ := hupd_part
  have hpush_part : ∃ y, ExecWithin w
      (ram[ if val2 < rn then [
              addr ← bStack + sp; *addr ← val2;
              sp ← sp + one
            ] else [ tmp ← zero ] ] : Code .standard 26) y₅ y 4 ∧
      BaseRegs n matBase eps scale M y ∧
      StackMem (matBase + 2 * (n * n) + 2 * n) s'.free y ∧
      (∀ a, a ≠ matBase + 2 * (n * n) + 2 * n + rest.length → y.mem a = y₅.mem a) := by
    refine WP.exists_execWithin ?_
    cases hoj : s.owner j₀ with
    | none =>
      have hv2_eq : y₅.regs val2 = n := by simpa [hoj, encodeOptFin] using hv2₅
      have hnl : ¬n < n := Nat.lt_irrefl n
      wram_exec [hb₅.hrn, hb₅.hzero, hv2_eq, hnl]
      refine ⟨hb₅.of_eq fun r hr => by wram_simp, ?_, fun _ _ => rfl⟩
      rw [hs'_eq]; simp only [hoj, Option.toList_none, List.nil_append]
      refine ⟨by wram_simp [hsp₅], fun t ht => ?_⟩
      wram_simp
      rw [hf₅ _ (by omega)]
      have ht' : t < s.free.length := by rw [hs, List.length_cons]; omega
      rw [hSM.2 t ht']
      simp only [hs, List.reverse_cons]
      rw [List.getElem_append_left (by simpa using ht)]
    | some i' =>
      have hi'_lt := i'.isLt
      have hv2_eq : y₅.regs val2 = i'.val := by simpa [hoj, encodeOptFin] using hv2₅
      have hf_sp1 : Fits w (rest.length + 1) := hfit.of_le (by omega)
      wram_exec [hb₅.hbStack, hb₅.hrn, hb₅.hone, hsp₅, hv2_eq, hi'_lt, hf_st_addr, hf_sp1]
      refine ⟨hb₅.of_eq fun r hr => by wram_simp, ?_, fun a ha => by wram_simp⟩
      rw [hs'_eq]; simp only [hoj, Option.toList_some, List.singleton_append]
      refine ⟨by wram_simp; simp, fun t ht => ?_⟩
      simp only [List.reverse_cons]
      have hlen_rev : rest.reverse.length = rest.length := List.length_reverse
      by_cases htt : t < rest.length
      · rw [List.getElem_append_left (by omega)]
        wram_simp
        rw [hf₅ _ (by omega)]
        have ht' : t < s.free.length := by rw [hs, List.length_cons]; omega
        rw [hSM.2 t ht']
        simp only [hs, List.reverse_cons]
        rw [List.getElem_append_left (by omega)]
      · have hteq : t = rest.length := by simp only [List.length_cons] at ht; omega
        subst hteq
        rw [List.getElem_append_right (by rw [hlen_rev])]
        wram_simp
        simp [hlen_rev]
  obtain ⟨y, he_push, hby, hSy, hf_push⟩ := hpush_part
  have hOy : OwnerMem (matBase + 2 * (n * n)) s'.owner y.mem := fun j =>
    (hf_push _ (by have := j.isLt; omega)).trans (hOy₅ j)
  have hPy : PriceMem (matBase + 2 * (n * n) + n) s'.price y.mem := fun j =>
    (hf_push _ (by have := j.isLt; omega)).trans (hPy₅ j)
  have hfy : ∀ a, ¬(matBase + 2 * (n * n) ≤ a ∧ a < matBase + 2 * (n * n) + 3 * n) →
      y.mem a = x.mem a := fun a ha =>
    (hf_push a (by omega)).trans (hf₅ a (by omega))
  exact ⟨y, (he_pop.seq (he_best.seq (he_sec.seq (he_p.seq (he_upd.seq he_push))))).mono (by omega),
    hby, hOy, hPy, hSy, hfy⟩

private theorem exec_bidLoop {w n matBase eps scale M W : ℕ}
    {C : Fin n × Fin n → ℕ} (hC : ∀ i j, C (i, j) ≤ W)
    (fuel : ℕ) :
    let cZ : Fin n × Fin n → ℤ := fun e => (C e : ℤ)
    ∀ (s : AuctionState n) (x : Data 26),
      AuctionInv cZ (eps : ℤ) s →
      (∀ k, 0 ≤ s.price k) →
      (auctionLoop cZ (eps : ℤ) fuel s).free = [] →
      BaseRegs n matBase eps scale M x →
      CostMem (matBase + n * n) C x.mem →
      OwnerMem (matBase + 2 * (n * n)) s.owner x.mem →
      PriceMem (matBase + 2 * (n * n) + n) s.price x.mem →
      StackMem (matBase + 2 * (n * n) + 2 * n) s.free x →
      Fits w (matBase + 2 * (n * n) + 4 * n + 2 * W + 2 * eps + 4) →
      ∃ y, ExecWithin w (.loop (.lt zero sp) bidStepCode) x y
          (((auctionLoop cZ (eps : ℤ) fuel s).bids - s.bids) * (28 * n + 30) + 2) ∧
        BaseRegs n matBase eps scale M y ∧
        OwnerMem (matBase + 2 * (n * n)) (auctionLoop cZ (eps : ℤ) fuel s).owner y.mem ∧
        PriceMem (matBase + 2 * (n * n) + n) (auctionLoop cZ (eps : ℤ) fuel s).price y.mem ∧
        (∀ a, ¬(matBase + 2 * (n * n) ≤ a ∧ a < matBase + 2 * (n * n) + 3 * n) →
          y.mem a = x.mem a) := by
  intro cZ
  induction fuel with
  | zero =>
    intro s x _ _ hfree hb _ hOM hPM hSM _
    rw [auctionLoop] at hfree
    have hc : ¬(Cond.lt zero sp).Holds x := by
      rw [Cond.holds_lt, hb.hzero, hSM.1, hfree]
      simp
    exact ⟨x, (ExecWithin.loop_exit hc).mono (by simp [auctionLoop]), hb, hOM, hPM,
      fun _ _ => rfl⟩
  | succ fuel ih =>
    intro s x hinv hp_nn hfree hb hCM hOM hPM hSM hfit
    rcases hs : s.free with _ | ⟨i₀, rest⟩
    · have hc : ¬(Cond.lt zero sp).Holds x := by
        rw [Cond.holds_lt, hb.hzero, hSM.1, hs]
        simp
      simpa [auctionLoop, hs] using
        ⟨x, (ExecWithin.loop_exit hc).mono (by simp), hb, hOM, hPM, fun _ _ => rfl⟩
    · have hc : (Cond.lt zero sp).Holds x := by
        rw [Cond.holds_lt, hb.hzero, hSM.1, hs, List.length_cons]
        omega
      obtain ⟨x₁, he_step, hb₁, hOM₁, hPM₁, hSM₁, hf₁⟩ :=
        exec_bidStepCode hC hs hinv hp_nn x hb hCM hOM hPM hSM hfit
      have hCM₁ : CostMem (matBase + n * n) C x₁.mem := hCM.of_outside fun a ha => hf₁ a (by omega)
      have hfree₁ : (auctionLoop cZ (eps : ℤ) fuel (bidStep cZ (eps : ℤ) s)).free = [] := by
        simpa [auctionLoop, hs] using hfree
      have hbids₁ : (bidStep cZ (eps : ℤ) s).bids = s.bids + 1 := bids_bidStep hs
      have hbids_le :
          (bidStep cZ (eps : ℤ) s).bids ≤
            (auctionLoop cZ (eps : ℤ) fuel (bidStep cZ (eps : ℤ) s)).bids :=
        bids_le_bids_auctionLoop cZ (eps : ℤ) fuel (bidStep cZ (eps : ℤ) s)
      obtain ⟨y, he_rec, hby, hOMy, hPMy, hfy⟩ :=
        ih (bidStep cZ (eps : ℤ) s) x₁ (hinv.bidStep (Nat.cast_nonneg eps))
          (price_nonneg_bidStep (Nat.cast_nonneg eps) hp_nn)
          hfree₁ hb₁ hCM₁ hOM₁ hPM₁ hSM₁ hfit
      have hsub_eq :
          (auctionLoop cZ (eps : ℤ) fuel (bidStep cZ (eps : ℤ) s)).bids - s.bids =
            ((auctionLoop cZ (eps : ℤ) fuel (bidStep cZ (eps : ℤ) s)).bids -
              (bidStep cZ (eps : ℤ) s).bids) + 1 := by
        omega
      refine ⟨y, (ExecWithin.loop_iter hc he_step he_rec).mono ?_, hby,
        by simpa [auctionLoop, hs] using hOMy,
        by simpa [auctionLoop, hs] using hPMy,
        fun a ha => (hfy a ha).trans (hf₁ a ha)⟩
      simp only [auctionLoop, hs, hsub_eq, Nat.add_mul, Nat.one_mul]
      omega

/-- **In-memory execution of `coreCode`**: starting with `BaseRegs` and `CostMem` for an unsigned
cost matrix `C` bounded by `W` and increment `eps > 0`, `coreCode` terminates at the exact pure
state `auction (fun e => (C e : ℤ)) (eps : ℤ)` within
`(auction c ε).bids * (28 * n + 30) + 17 * n + 12` instructions. -/
theorem core_exec {w n matBase eps scale M W : ℕ} (hε : 0 < eps)
    {C : Fin n × Fin n → ℕ} (hC : ∀ i j, C (i, j) ≤ W)
    (x : Data 26) (hb : BaseRegs n matBase eps scale M x)
    (hCM : CostMem (matBase + n * n) C x.mem)
    (hfit : Fits w (matBase + 2 * (n * n) + 4 * n + 2 * W + 2 * eps + 4)) :
    let s := auction (fun e => (C e : ℤ)) (eps : ℤ)
    ∃ y, ExecWithin w coreCode x y (s.bids * (28 * n + 30) + 17 * n + 12) ∧
      BaseRegs n matBase eps scale M y ∧
      CostMem (matBase + n * n) C y.mem ∧
      (∀ j : Fin n, y.mem (matBase + 2 * (n * n) + j.val) =
        match s.owner j with | some i => i.val | none => n) ∧
      (∀ j : Fin n, y.mem (matBase + 2 * (n * n) + n + j.val) = (s.price j).toNat) := by
  intro s
  obtain ⟨x₁, he_init, hb₁, hOM₁, hPM₁, hSM₁, hf₁⟩ :=
    exec_initCoreCode x hb (hfit.of_le (by omega))
  have hCM₁ : CostMem (matBase + n * n) C x₁.mem := hCM.of_outside fun a ha => hf₁ a (by omega)
  let cZ : Fin n × Fin n → ℤ := fun e => (C e : ℤ)
  have hfree :
      (auctionLoop cZ (eps : ℤ) (bidBound n (costSpread cZ) (eps : ℤ)) (auctionInit n)).free =
        [] := auction_free (Nat.cast_pos.mpr hε)
  obtain ⟨y, he_loop, hby, hOMy, hPMy, hfy⟩ :=
    exec_bidLoop hC (bidBound n (costSpread cZ) (eps : ℤ)) (auctionInit n) x₁
      auctionInv_init (fun _ => le_rfl) hfree hb₁ hCM₁ hOM₁ hPM₁ hSM₁ hfit
  have hCM_y : CostMem (matBase + n * n) C y.mem :=
    hCM₁.of_outside fun a ha => hfy a (by omega)
  refine ⟨y, (he_init.seq he_loop).mono ?_, hby, hCM_y,
    fun j => by
      have hj : y.mem (matBase + 2 * (n * n) + j.val) = encodeOptFin (s.owner j) := hOMy j
      cases h : s.owner j <;> simpa [encodeOptFin, h] using hj,
    hPMy⟩
  change (17 * n + 10) + ((s.bids - 0) * (28 * n + 30) + 2) ≤ _
  simp only [Nat.sub_zero]
  omega

/-! ## Section 4: Shared input scan/shift, output scatter, and `State.init` endpoints -/

private def scanMaxBody : Code .standard 26 := ram[
  addr ← matBaseReg + idx; val ← *addr;
  val ← val / two;
  if rM < val then [ rM ← val ] else [ tmp ← zero ];
  idx ← idx + one ]

private def scanMaxCode : Code .standard 26 :=
  .seq (ram[ rM ← #0; idx ← #0 ]) (.loop (.lt idx rnn) scanMaxBody)

private def fillCBody : Code .standard 26 := ram[
  addr ← matBaseReg + idx; val ← *addr;
  val2 ← val % two;
  val ← val / two;
  if val2 = one then [ val ← rM - val ] else [ val ← rM + val ];
  val ← rscale * val;
  addr ← bC + idx; *addr ← val;
  idx ← idx + one ]

private def fillCCode : Code .standard 26 :=
  .seq (ram[ idx ← #0 ]) (.loop (.lt idx rnn) fillCBody)

private def setupRegsCode (isScaled : Bool) : Code .standard 26 :=
  .seq (ram[ zero ← #0; one ← #1; two ← #2; addr ← #1; rn ← *addr; rnn ← rn * rn ])
    (.seq (if isScaled then
             ram[ reps ← #1; rscale ← rn + one; matBaseReg ← #2 ]
           else
             ram[ addr ← #2; reps ← *addr; rscale ← #1; matBaseReg ← #3 ])
      (ram[ bC ← matBaseReg + rnn;
            bOwner ← bC + rnn;
            bPrice ← bOwner + rn;
            bStack ← bPrice + rn;
            outBase ← bStack + rn ]))

private def setupAndFillCode (isScaled : Bool) : Code .standard 26 :=
  .seq (setupRegsCode isScaled) (.seq scanMaxCode fillCCode)

private theorem exec_setupRegsCode {w n eps : ℕ} (isScaled : Bool)
    (input : List ℕ) (hn : (Data.init input : Data 26).mem 1 = n)
    (heps : isScaled = false → (Data.init input : Data 26).mem 2 = eps)
    (hfit : Fits w ((if isScaled then 2 else 3) + 2 * (n * n) + 3 * n + 4)) :
    ∃ y₁, ExecWithin w (setupRegsCode isScaled) (Data.init input) y₁ 15 ∧
      BaseRegs n (if isScaled then 2 else 3) (if isScaled then 1 else eps)
        (if isScaled then n + 1 else 1) (y₁.regs rM) y₁ ∧
      y₁.mem = (Data.init input : Data 26).mem := by
  let matBase := if isScaled then 2 else 3
  have hf_bound : ∀ k, k ≤ matBase + 2 * (n * n) + 3 * n + 4 → Fits w k :=
    fun _ hk => hfit.of_le hk
  have hmb_pos : 2 ≤ matBase := by cases isScaled <;> simp [matBase]
  have hf0 : Fits w 0 := hf_bound 0 (by omega)
  have hf1 : Fits w 1 := hf_bound 1 (by omega)
  have hf2 : Fits w 2 := hf_bound 2 (by omega)
  have hf3 : Fits w 3 := hf_bound 3 (by omega)
  have hfnn : Fits w (n * n) := hf_bound (n * n) (by omega)
  have hfbC : Fits w (matBase + n * n) := hf_bound _ (by omega)
  have hfbO : Fits w (matBase + n * n + n * n) := hf_bound _ (by omega)
  have hfbP : Fits w (matBase + n * n + n * n + n) := hf_bound _ (by omega)
  have hfbS : Fits w (matBase + n * n + n * n + n + n) := hf_bound _ (by omega)
  have hfOb : Fits w (matBase + n * n + n * n + n + n + n) := hf_bound _ (by omega)
  cases isScaled with
  | true =>
    have hfn1 : Fits w (n + 1) := hf_bound _ (by omega)
    simp only [setupRegsCode, matBase, ↓reduceIte] at hfbC hfbO hfbP hfbS hfOb ⊢
    refine WP.exists_execWithin ?_
    wram_exec [hn, hf0, hf1, hf2, hfnn, hfn1, hfbC, hfbO, hfbP, hfbS, hfOb]
    refine ⟨?_, rfl⟩
    exact
      { hzero := by wram_simp
        hone := by wram_simp
        htwo := by wram_simp
        hrn := by wram_simp
        hrnn := by wram_simp
        hreps := by wram_simp
        hrscale := by wram_simp
        hrM := rfl
        hmatBase := by wram_simp
        hbC := by wram_simp
        hbOwner := by wram_simp; omega
        hbPrice := by wram_simp; omega
        hbStack := by wram_simp; omega
        houtBase := by wram_simp; omega }
  | false =>
    have heps_mem := heps rfl
    simp only [setupRegsCode, matBase, Bool.false_eq_true, ↓reduceIte]
      at hfbC hfbO hfbP hfbS hfOb ⊢
    refine WP.exists_execWithin ?_
    wram_exec [hn, heps_mem, hf0, hf1, hf2, hf3, hfnn, hfbC, hfbO, hfbP, hfbS, hfOb]
    refine ⟨?_, rfl⟩
    exact
      { hzero := by wram_simp
        hone := by wram_simp
        htwo := by wram_simp
        hrn := by wram_simp
        hrnn := by wram_simp
        hreps := by wram_simp
        hrscale := by wram_simp
        hrM := rfl
        hmatBase := by wram_simp
        hbC := by wram_simp
        hbOwner := by wram_simp; omega
        hbPrice := by wram_simp; omega
        hbStack := by wram_simp; omega
        houtBase := by wram_simp; omega }

private theorem exec_scanMaxCode {w n matBase effEps scale M₀ maxMag : ℕ}
    (cost : Fin n × Fin n → ℤ) (y₁ : Data 26)
    (hb₁ : BaseRegs n matBase effEps scale M₀ y₁)
    (hmag : ∀ i j : Fin n, (cost (i, j)).natAbs ≤ maxMag)
    (hmat : ∀ i j : Fin n, y₁.mem (matBase + (i.val * n + j.val)) = Signed.encode (cost (i, j)))
    (hfit : Fits w (matBase + n * n + maxMag + 1)) :
    ∃ y₂ M, ExecWithin w scanMaxCode y₁ y₂ (9 * (n * n) + 4) ∧
      M ≤ maxMag ∧
      (∀ i j : Fin n, (cost (i, j)).natAbs ≤ M) ∧
      BaseRegs n matBase effEps scale M y₂ ∧
      y₂.mem = y₁.mem := by
  let PM (k : ℕ) (y : Data 26) : Prop :=
    k ≤ n * n ∧
      (∀ r : Fin 26, r.val < 14 → r ≠ rM → y.regs r = y₁.regs r) ∧
      y.mem = y₁.mem ∧
      y.regs rM ≤ maxMag ∧
      (∀ q : ℕ, (hq : q < k) → (hq' : q < n * n) →
        (cost (finProdFinEquiv.symm ⟨q, hq'⟩)).natAbs ≤ y.regs rM)
  have hs_m₀ : ∃ sm, ExecWithin w (ram[ rM ← #0; idx ← #0 ] : Code .standard 26) y₁ sm 2 ∧
      sm = (y₁.set rM 0).set idx 0 := by
    refine WP.exists_execWithin ?_; wram_exec; rfl
  obtain ⟨sm, he_m₀, rfl⟩ := hs_m₀
  have hPM₀ : PM 0 ((y₁.set rM 0).set idx 0) :=
    ⟨Nat.zero_le _, fun _ _ _ => by wram_simp, rfl, by wram_simp; exact Nat.zero_le _,
      fun _ hq _ => absurd hq (Nat.not_lt_zero _)⟩
  have hbodyM (y : Data 26) (hy : PM (y.regs idx) y) (hlt : y.regs idx < n * n) :
      ∃ z, ExecWithin w scanMaxBody y z 7 ∧ PM (y.regs idx + 1) z ∧
        z.regs idx = y.regs idx + 1 := by
    obtain ⟨_, hr, hmem, hM_le, hM_ge⟩ := hy
    let p := finProdFinEquiv.symm ⟨y.regs idx, hlt⟩
    have hp_mul : p.1.val * n + p.2.val = y.regs idx :=
      (Cslib.Matrix.pairIndex_eq_val_finProdFinEquiv p).trans
        (congrArg Fin.val (finProdFinEquiv.apply_symm_apply ⟨y.regs idx, hlt⟩))
    have hy_mb : y.regs matBaseReg = matBase :=
      (hr matBaseReg (by decide) (by decide)).trans hb₁.hmatBase
    have hy_two : y.regs two = 2 := (hr two (by decide) (by decide)).trans hb₁.htwo
    have hy_zero : y.regs zero = 0 := (hr zero (by decide) (by decide)).trans hb₁.hzero
    have hy_one : y.regs one = 1 := (hr one (by decide) (by decide)).trans hb₁.hone
    have hload : y.mem (matBase + y.regs idx) = Signed.encode (cost (p.1, p.2)) := by
      rw [hmem, ← hp_mul]; exact hmat p.1 p.2
    have hdiv : Signed.encode (cost (p.1, p.2)) / 2 = (cost (p.1, p.2)).natAbs :=
      Signed.encode_div_two _
    have hmag_p : (cost (p.1, p.2)).natAbs ≤ maxMag := hmag p.1 p.2
    have hf_a : Fits w (matBase + y.regs idx) := hfit.of_le (by omega)
    have hf_v : Fits w (cost (p.1, p.2)).natAbs := hfit.of_le (by omega)
    have hf_i1 : Fits w (y.regs idx + 1) := hfit.of_le (by omega)
    refine WP.exists_execWithin ?_
    unfold scanMaxBody
    by_cases hcmp : y.regs rM < (cost (p.1, p.2)).natAbs
    · wram_exec [hy_mb, hy_two, hy_zero, hy_one, hload, hdiv, hcmp, hf_a, hf_v, hf_i1]
      refine ⟨⟨by omega, fun r hr' hne => by wram_simp [hr r hr' hne], hmem,
        by wram_simp; exact hmag_p, fun q hq hq' => ?_⟩, by wram_simp⟩
      wram_simp
      rcases eq_or_ne q (y.regs idx) with rfl | hne
      · exact le_rfl
      · exact (hM_ge q (by omega) hq').trans (le_of_lt hcmp)
    · wram_exec [hy_mb, hy_two, hy_zero, hy_one, hload, hdiv, hcmp, hf_a, hf_v, hf_i1]
      refine ⟨⟨by omega, fun r hr' hne => by wram_simp [hr r hr' hne], hmem,
        by wram_simp; exact hM_le, fun q hq hq' => ?_⟩, by wram_simp⟩
      wram_simp
      rcases eq_or_ne q (y.regs idx) with rfl | hne
      · exact le_of_not_gt hcmp
      · exact hM_ge q (by omega) hq'
  obtain ⟨y₂, hl_m, hPMn, _⟩ := ExecWithin.loop_count PM
    (fun y hy => (hy.2.1 rnn (by decide) (by decide)).trans hb₁.hrnn) hbodyM
    (x := (y₁.set rM 0).set idx 0) (by simp) (by simpa using hPM₀)
  obtain ⟨_, hr₂, hmem₂, hM_le, hM_ge_q⟩ := hPMn
  let M := y₂.regs rM
  have hM_ge : ∀ i j : Fin n, (cost (i, j)).natAbs ≤ M := fun i j => by
    have hq : i.val * n + j.val < n * n := Cslib.Matrix.pairIndex_lt (i, j)
    have h := hM_ge_q (i.val * n + j.val) hq hq
    have hp_eq : (⟨i.val * n + j.val, hq⟩ : Fin (n * n)) = finProdFinEquiv (i, j) :=
      Fin.ext (Cslib.Matrix.pairIndex_eq_val_finProdFinEquiv (i, j))
    rwa [hp_eq, finProdFinEquiv.symm_apply_apply] at h
  have hb₂ : BaseRegs n matBase effEps scale M y₂ :=
    { hzero := (hr₂ zero (by decide) (by decide)).trans hb₁.hzero
      hone := (hr₂ one (by decide) (by decide)).trans hb₁.hone
      htwo := (hr₂ two (by decide) (by decide)).trans hb₁.htwo
      hrn := (hr₂ rn (by decide) (by decide)).trans hb₁.hrn
      hrnn := (hr₂ rnn (by decide) (by decide)).trans hb₁.hrnn
      hreps := (hr₂ reps (by decide) (by decide)).trans hb₁.hreps
      hrscale := (hr₂ rscale (by decide) (by decide)).trans hb₁.hrscale
      hrM := rfl
      hmatBase := (hr₂ matBaseReg (by decide) (by decide)).trans hb₁.hmatBase
      hbC := (hr₂ bC (by decide) (by decide)).trans hb₁.hbC
      hbOwner := (hr₂ bOwner (by decide) (by decide)).trans hb₁.hbOwner
      hbPrice := (hr₂ bPrice (by decide) (by decide)).trans hb₁.hbPrice
      hbStack := (hr₂ bStack (by decide) (by decide)).trans hb₁.hbStack
      houtBase := (hr₂ outBase (by decide) (by decide)).trans hb₁.houtBase }
  exact ⟨y₂, M, (he_m₀.seq hl_m).mono (by simp; omega), hM_le, hM_ge, hb₂, hmem₂⟩

private theorem exec_fillCCode {w n matBase effEps scale M : ℕ}
    (hscale : 1 ≤ scale) (cost : Fin n × Fin n → ℤ) (y₂ : Data 26)
    (hb₂ : BaseRegs n matBase effEps scale M y₂)
    (hM_ge : ∀ i j : Fin n, (cost (i, j)).natAbs ≤ M)
    (hmat : ∀ i j : Fin n, y₂.mem (matBase + (i.val * n + j.val)) = Signed.encode (cost (i, j)))
    (hfit : Fits w (matBase + 2 * (n * n) + 2 * scale * M + 1)) :
    ∃ y, ExecWithin w fillCCode y₂ y (13 * (n * n) + 3) ∧
      BaseRegs n matBase effEps scale M y ∧
      CostMem (matBase + n * n) (fun p => scale * (cost p + (M : ℤ)).toNat) y.mem := by
  let Cw : Fin n × Fin n → ℕ := fun p => scale * (cost p + (M : ℤ)).toNat
  let eC : ℕ → ℕ := fun q => if hq : q < n * n then Cw (finProdFinEquiv.symm ⟨q, hq⟩) else 0
  have hs_c₀ : ∃ sc, ExecWithin w (ram[ idx ← #0 ] : Code .standard 26) y₂ sc 1 ∧
      sc = y₂.set idx 0 := by
    refine WP.exists_execWithin ?_; wram_exec; rfl
  obtain ⟨sc, he_c₀, rfl⟩ := hs_c₀
  let PC (k : ℕ) (y : Data 26) : Prop :=
    k ≤ n * n ∧
      (∀ r : Fin 26, r.val < 14 → y.regs r = y₂.regs r) ∧
      (∀ j < k, y.mem (matBase + n * n + j) = eC j) ∧
      (∀ a, ¬(matBase + n * n ≤ a ∧ a < matBase + n * n + k) → y.mem a = y₂.mem a)
  have hPC₀ : PC 0 (y₂.set idx 0) :=
    ⟨Nat.zero_le _, fun _ _ => by wram_simp, fun _ hj => absurd hj (Nat.not_lt_zero _),
      fun _ _ => rfl⟩
  have hbodyC (y : Data 26) (hy : PC (y.regs idx) y) (hlt : y.regs idx < n * n) :
      ∃ z, ExecWithin w fillCBody y z 11 ∧ PC (y.regs idx + 1) z ∧
        z.regs idx = y.regs idx + 1 := by
    obtain ⟨_, hr, hm, hf⟩ := hy
    have hby : BaseRegs n matBase effEps scale M y := hb₂.of_eq hr
    let p := finProdFinEquiv.symm ⟨y.regs idx, hlt⟩
    have hp_mul : p.1.val * n + p.2.val = y.regs idx :=
      (Cslib.Matrix.pairIndex_eq_val_finProdFinEquiv p).trans
        (congrArg Fin.val (finProdFinEquiv.apply_symm_apply ⟨y.regs idx, hlt⟩))
    have hload : y.mem (matBase + y.regs idx) = Signed.encode (cost (p.1, p.2)) := by
      rw [hf _ (by omega), ← hp_mul]; exact hmat p.1 p.2
    have hdiv : Signed.encode (cost (p.1, p.2)) / 2 = (cost (p.1, p.2)).natAbs :=
      Signed.encode_div_two _
    have hmod : Signed.encode (cost (p.1, p.2)) % 2 =
        if cost (p.1, p.2) < 0 then 1 else 0 := Signed.encode_mod_two _
    have hmag_M : (cost (p.1, p.2)).natAbs ≤ M := hM_ge p.1 p.2
    have hM_fit : M ≤ scale * M := by
      calc M = 1 * M := by omega
        _ ≤ scale * M := Nat.mul_le_mul_right M hscale
    have hf_a : Fits w (matBase + y.regs idx) := hfit.of_le (by omega)
    have hf_v : Fits w (cost (p.1, p.2)).natAbs := hfit.of_le (by nlinarith)
    have hf_bc : Fits w (matBase + n * n + y.regs idx) := hfit.of_le (by omega)
    have hf_i1 : Fits w (y.regs idx + 1) := hfit.of_le (by omega)
    refine WP.exists_execWithin ?_
    unfold fillCBody
    by_cases hneg : cost (p.1, p.2) < 0
    · have hmod1 : (if cost (p.1, p.2) < 0 then 1 else 0) = 1 := ite_eq_left hneg
      have hsh_eq : M - (cost (p.1, p.2)).natAbs = (cost (p.1, p.2) + (M : ℤ)).toNat := by omega
      have hsh_le : M - (cost (p.1, p.2)).natAbs ≤ M := Nat.sub_le _ _
      have hmul_le : scale * (M - (cost (p.1, p.2)).natAbs) ≤ scale * M :=
        Nat.mul_le_mul_left scale hsh_le
      have hf_sh : Fits w (M - (cost (p.1, p.2)).natAbs) := hfit.of_le (by nlinarith)
      have hf_sc : Fits w (scale * (M - (cost (p.1, p.2)).natAbs)) := hfit.of_le (by nlinarith)
      wram_exec [hby.hmatBase, hby.htwo, hby.hone, hby.hrM, hby.hrscale, hby.hbC,
        hload, hdiv, hmod, hmod1, hmag_M, hf_a, hf_v, hf_sh, hf_sc, hf_bc, hf_i1]
      refine ⟨⟨by omega, fun r hr' => by wram_simp [hr r hr'], fun j hj => ?_, fun a ha => ?_⟩,
        by wram_simp⟩
      · by_cases hjeq : j = y.regs idx
        · subst hjeq; wram_simp; simp only [eC, hlt, dite_true, Cw, ← hsh_eq, p, Prod.mk.eta]
        · wram_simp; exact hm j (by omega)
      · wram_simp; exact hf a (by omega)
    · have hmod0 : (if cost (p.1, p.2) < 0 then 1 else 0) = 0 := ite_eq_right hneg
      have hsh_eq : M + (cost (p.1, p.2)).natAbs = (cost (p.1, p.2) + (M : ℤ)).toNat := by omega
      have hsh_le : M + (cost (p.1, p.2)).natAbs ≤ 2 * M := by omega
      have hsh_fit : M + (cost (p.1, p.2)).natAbs ≤ 2 * scale * M := by
        calc M + (cost (p.1, p.2)).natAbs ≤ 2 * M := hsh_le
          _ ≤ 2 * (scale * M) := Nat.mul_le_mul_left 2 hM_fit
          _ = 2 * scale * M := by ring
      have hmul_le : scale * (M + (cost (p.1, p.2)).natAbs) ≤ 2 * scale * M := by
        calc scale * (M + (cost (p.1, p.2)).natAbs) ≤ scale * (2 * M) :=
              Nat.mul_le_mul_left scale hsh_le
          _ = 2 * scale * M := by ring
      have hf_sh : Fits w (M + (cost (p.1, p.2)).natAbs) := hfit.of_le (by omega)
      have hf_sc : Fits w (scale * (M + (cost (p.1, p.2)).natAbs)) := hfit.of_le (by omega)
      wram_exec [hby.hmatBase, hby.htwo, hby.hone, hby.hrM, hby.hrscale, hby.hbC,
        hload, hdiv, hmod, hmod0, hf_a, hf_v, hf_sh, hf_sc, hf_bc, hf_i1]
      refine ⟨⟨by omega, fun r hr' => by wram_simp [hr r hr'], fun j hj => ?_, fun a ha => ?_⟩,
        by wram_simp⟩
      · by_cases hjeq : j = y.regs idx
        · subst hjeq; wram_simp; simp only [eC, hlt, dite_true, Cw, ← hsh_eq, p, Prod.mk.eta]
        · wram_simp; exact hm j (by omega)
      · wram_simp; exact hf a (by omega)
  obtain ⟨y, hl_c, hPCn, _⟩ := ExecWithin.loop_count PC
    (fun y hy => (hy.2.1 rnn (by decide)).trans hb₂.hrnn) hbodyC
    (x := y₂.set idx 0) (by simp) (by simpa using hPC₀)
  obtain ⟨_, hr_y, hm_y, _⟩ := hPCn
  have hCM_y : CostMem (matBase + n * n) Cw y.mem :=
    { hentry := fun i j => by
        have hq : i.val * n + j.val < n * n := Cslib.Matrix.pairIndex_lt (i, j)
        rw [hm_y (i.val * n + j.val) hq]
        simp only [eC, hq, dite_true]
        have hp_eq : (⟨i.val * n + j.val, hq⟩ : Fin (n * n)) = finProdFinEquiv (i, j) :=
          Fin.ext (Cslib.Matrix.pairIndex_eq_val_finProdFinEquiv (i, j))
        rw [hp_eq, finProdFinEquiv.symm_apply_apply] }
  exact ⟨y, (he_c₀.seq hl_c).mono (by simp; omega), hb₂.of_eq hr_y, hCM_y⟩

private theorem exec_setupAndFillCode {w n eps : ℕ} (isScaled : Bool)
    (cost : Fin n × Fin n → ℤ) (input : List ℕ) (maxMag : ℕ)
    (hmag : ∀ i j : Fin n, (cost (i, j)).natAbs ≤ maxMag)
    (hn : (Data.init input : Data 26).mem 1 = n)
    (heps : isScaled = false → (Data.init input : Data 26).mem 2 = eps)
    (hmat : ∀ i j : Fin n,
      (Data.init input : Data 26).mem ((if isScaled then 2 else 3) + (i.val * n + j.val)) =
        Signed.encode (cost (i, j)))
    (hfit : Fits w ((if isScaled then 2 else 3) + 2 * (n * n) + 4 * n +
      2 * (if isScaled then n + 1 else 1) * maxMag + 4)) :
    ∃ y M, ExecWithin w (setupAndFillCode isScaled) (Data.init input) y
        (22 * (n * n) + 22) ∧
      M ≤ maxMag ∧
      (∀ i j : Fin n, (cost (i, j)).natAbs ≤ M) ∧
      BaseRegs n (if isScaled then 2 else 3) (if isScaled then 1 else eps)
        (if isScaled then n + 1 else 1) M y ∧
      CostMem ((if isScaled then 2 else 3) + n * n)
        (fun p => (if isScaled then n + 1 else 1) * (cost p + (M : ℤ)).toNat) y.mem := by
  have hscale : 1 ≤ if isScaled then n + 1 else 1 := by cases isScaled <;> simp
  obtain ⟨y₁, he_pre, hb₁, hmem₁⟩ :=
    exec_setupRegsCode isScaled input hn heps
      (hfit.of_le (by cases isScaled <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> nlinarith))
  obtain ⟨y₂, M, he_m, hM_le, hM_ge, hb₂, hmem₂⟩ :=
    exec_scanMaxCode cost y₁ hb₁ hmag (fun i j => hmem₁ ▸ hmat i j)
      (hfit.of_le (by cases isScaled <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> nlinarith))
  obtain ⟨y, he_c, hb_y, hCM_y⟩ :=
    exec_fillCCode hscale cost y₂ hb₂ hM_ge (fun i j => (hmem₂.trans hmem₁) ▸ hmat i j)
      (hfit.of_le (by cases isScaled <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> nlinarith))
  exact ⟨y, M, (he_pre.seq (he_m.seq he_c)).mono (by omega), hM_le, hM_ge, hb_y, hCM_y⟩

private def scatterOutputBody : Code .standard 26 := ram[
  addr ← bOwner + idx; val ← *addr;
  addr ← outBase + one; addr ← addr + val; *addr ← idx;
  idx ← idx + one ]

private def scatterOutputCode : Code .standard 26 :=
  .seq (ram[ addr ← outBase; *addr ← rn; idx ← #0 ])
    (.loop (.lt idx rn) scatterOutputBody)

private theorem exec_scatterOutputCode {w n matBase eps scale M : ℕ}
    {cZ : Fin n × Fin n → ℤ} {εZ : ℤ} {s : AuctionState n}
    (hinv : AuctionInv cZ εZ s) (hfree : s.free = [])
    (x : Data 26) (hb : BaseRegs n matBase eps scale M x)
    (hOM : ∀ j : Fin n, x.mem (matBase + 2 * (n * n) + j.val) =
      match s.owner j with | some i => i.val | none => n)
    (hfit : Fits w (matBase + 2 * (n * n) + 4 * n + 2)) :
    ∃ z, ExecWithin w scatterOutputCode x z (8 * n + 5) ∧
      BaseRegs n matBase eps scale M z ∧
      outputList z.mem (z.regs outBase) =
        ((List.finRange n).map fun i => (s.objectOf i).val) ∧
      Fits w (z.regs outBase + n) ∧
      (∀ a, ¬(matBase + 2 * (n * n) + 3 * n ≤ a ∧ a < matBase + 2 * (n * n) + 4 * n + 1) →
        z.mem a = x.mem a) := by
  let bOut := matBase + 2 * (n * n) + 3 * n
  have hf_ob : Fits w bOut := hfit.of_le (by dsimp only [bOut]; omega)
  have hs₀ : ∃ s₀, ExecWithin w
      (ram[ addr ← outBase; *addr ← rn; idx ← #0 ] : Code .standard 26) x s₀ 3 ∧
      s₀ = ((x.set addr bOut).write bOut n).set idx 0 := by
    refine WP.exists_execWithin ?_
    wram_exec [hb.houtBase, hb.hrn, hf_ob]
    rfl
  obtain ⟨s₀, he₀, rfl⟩ := hs₀
  let s₀ := ((x.set addr bOut).write bOut n).set idx 0
  let PO (t : ℕ) (y : Data 26) : Prop :=
    t ≤ n ∧
      (∀ r : Fin 26, r.val < 14 → y.regs r = x.regs r) ∧
      y.mem bOut = n ∧
      (∀ (j i : Fin n), j.val < t → s.owner j = some i → y.mem (bOut + 1 + i.val) = j.val) ∧
      (∀ a, ¬(bOut ≤ a ∧ a < bOut + 1 + n) → y.mem a = x.mem a)
  have hPO₀ : PO 0 s₀ :=
    ⟨Nat.zero_le _, fun _ _ => by dsimp only [s₀]; wram_simp,
      by dsimp only [s₀]; wram_simp,
      fun _ _ hj => absurd hj (Nat.not_lt_zero _),
      fun a ha => by dsimp only [s₀]; wram_simp⟩
  have hbody (y : Data 26) (hy : PO (y.regs idx) y) (hlt : y.regs idx < n) :
      ∃ z, ExecWithin w scatterOutputBody y z 6 ∧ PO (y.regs idx + 1) z ∧
        z.regs idx = y.regs idx + 1 := by
    obtain ⟨_, hr, hob, hsome, hf⟩ := hy
    have hby : BaseRegs n matBase eps scale M y := hb.of_eq hr
    let j₀ : Fin n := ⟨y.regs idx, hlt⟩
    -- Since `s.free = []`, `j₀` is owned by `s.personOf j₀`!
    have hobj_pers : s.objectOf (s.personOf j₀) = j₀ := hinv.objectOf_personOf hfree j₀
    have hown_j₀ : s.owner j₀ = some (s.personOf j₀) := by
      have := hinv.owner_objectOf hfree (s.personOf j₀)
      rwa [hobj_pers] at this
    let i₀ : Fin n := s.personOf j₀
    have hi₀_lt := i₀.isLt
    have hmem_oj : y.mem (matBase + 2 * (n * n) + y.regs idx) = i₀.val := by
      rw [hf _ (by dsimp only [bOut]; omega), hOM j₀, hown_j₀]
    have hf_oj : Fits w (matBase + 2 * (n * n) + y.regs idx) := hfit.of_le (by omega)
    have hf_o1 : Fits w (bOut + 1) := hfit.of_le (by dsimp only [bOut]; omega)
    have hf_oi : Fits w ((bOut + 1) + i₀.val) := hfit.of_le (by dsimp only [bOut]; omega)
    have hf_idx1 : Fits w (y.regs idx + 1) := hfit.of_le (by omega)
    refine WP.exists_execWithin ?_
    unfold scatterOutputBody
    wram_exec [hby.hbOwner, hby.houtBase, hby.hone, hmem_oj, hf_oj, hf_o1, hf_oi, hf_idx1]
    refine ⟨⟨by omega, fun r hr' => by wram_simp [hr r hr'], by wram_simp [hob],
      fun j i hj hm => ?_, fun a ha => ?_⟩, by wram_simp⟩
    · by_cases hjj : j = j₀
      · subst hjj
        rw [hown_j₀] at hm
        obtain ⟨rfl⟩ := hm
        dsimp only [j₀]
        wram_simp
      · have hj_lt : j.val < y.regs idx := by
          have : j.val ≠ y.regs idx := fun h => hjj (Fin.ext h)
          omega
        have hii : i ≠ i₀ := fun h => by
          subst h
          exact hjj (hinv.owner_inj j j₀ i₀ hm hown_j₀)
        have hne_val : i.val ≠ i₀.val := fun h => hii (Fin.ext h)
        wram_simp
        exact hsome j i hj_lt hm
    · wram_simp; exact hf a ha
  have hs₀_idx : s₀.regs idx = 0 := by dsimp only [s₀]; wram_simp
  obtain ⟨z, hl, hPOn, _⟩ := ExecWithin.loop_count PO
    (fun y hy => (hy.2.1 rn (by decide)).trans hb.hrn) hbody
    (x := s₀) (by rw [hs₀_idx]; exact Nat.zero_le n) (by rw [hs₀_idx]; exact hPO₀)
  obtain ⟨_, hr_z, hob_z, hsome_z, hf_z⟩ := hPOn
  have hbz : BaseRegs n matBase eps scale M z := hb.of_eq hr_z
  have hout_z : outputList z.mem (z.regs outBase) =
      ((List.finRange n).map fun i => (s.objectOf i).val) := by
    rw [hbz.houtBase, outputList_eq_iff]
    simp only [List.length_map, List.length_finRange]
    refine ⟨hob_z, fun i => ?_⟩
    have hi_lt : i.val < n := by simpa using i.isLt
    let i_fin : Fin n := ⟨i.val, hi_lt⟩
    have hown_i : s.owner (s.objectOf i_fin) = some i_fin := hinv.owner_objectOf hfree i_fin
    change z.mem (bOut + 1 + i_fin.val) = ((List.finRange n).map fun k => (s.objectOf k).val)[i.val]
    rw [hsome_z (s.objectOf i_fin) i_fin (s.objectOf i_fin).isLt hown_i]
    simp [i_fin]
  have hfit_out : Fits w (z.regs outBase + n) := by
    rw [hbz.houtBase]; exact hfit.of_le (by omega)
  exact ⟨z, (he₀.seq hl).mono (by rw [hs₀_idx]; omega), hbz, hout_z, hfit_out,
    fun a ha => hf_z a (by dsimp only [bOut]; omega)⟩

/-! ### 4A. Unscaled `ε`-auction (`O(n² (C / ε + 1))`) -/

private def epsAuctionCode : Code .standard 26 :=
  .seq (setupAndFillCode false) (.seq coreCode scatterOutputCode)

/-- Standard-basis word-RAM program computing `EpsInstance.assignment` (`ExecutesList`) via
Bertsekas's Gauss–Seidel `ε`-auction. -/
def epsAuctionProgram : Program .standard 26 :=
  epsAuctionCode.program outBase

/-- Instruction bound `O(n² (C / ε + 1))` for `epsAuctionProgram` when `C` bounds the row cost
ranges ([Bertsekas1988], §1). -/
@[expose] def epsAuctionTime (n C eps : ℕ) : ℕ :=
  (n * (C + eps) / eps + 1) * (28 * n + 30) + 22 * (n * n) + 25 * n + 42

/-- **`O(n² (C / ε + 1))` Word-RAM `ε`-auction (`ExecutesList`).** Whenever `0 < inst.eps`, `C`
bounds every row cost range `inst.cost (i, k) - inst.cost (i, j) ≤ C`, and `Fits w inst.wordBound`,
`epsAuctionProgram` halts within `epsAuctionTime inst.n C inst.eps` instructions returning
`inst.assignment` (`n * eps`-optimal by `sum_auctionPerm_le`). -/
theorem executesList_epsAuction {w : ℕ} (inst : EpsInstance) (hε : 0 < inst.eps)
    {C : ℕ} (hC : ∀ i j k : Fin inst.n, inst.cost (i, k) - inst.cost (i, j) ≤ (C : ℤ))
    (hw : Fits w inst.wordBound) :
    ∃ steps, ExecutesList w epsAuctionProgram (.init inst.encode) inst.assignment steps ∧
      steps ≤ epsAuctionTime inst.n C inst.eps := by
  obtain ⟨y₁, M, he_sf, hM_le, hM_ge, hb₁, hCM₁⟩ :=
    exec_setupAndFillCode (n := inst.n) (eps := inst.eps) false inst.cost inst.encode inst.maxMag
      inst.toInstance.natAbs_cost_le_maxMag inst.init_mem_n (fun _ => inst.init_mem_eps)
      inst.init_mem_cost
      (hw.of_le (by
        simp only [Bool.false_eq_true, ↓reduceIte, mul_one]
        unfold EpsInstance.wordBound EpsInstance.maxMag
        nlinarith))
  simp only [Bool.false_eq_true, ↓reduceIte] at hb₁ hCM₁
  let C_nat : Fin inst.n × Fin inst.n → ℕ := fun p => 1 * (inst.cost p + (M : ℤ)).toNat
  have hC_le : ∀ i j : Fin inst.n, C_nat (i, j) ≤ 2 * M := fun i j => by
    have := hM_ge i j; dsimp only [C_nat]; omega
  have hC_cast : (fun e => (C_nat e : ℤ)) = fun e => inst.cost e + (M : ℤ) := by
    funext ⟨i, j⟩; have := hM_ge i j; dsimp only [C_nat]; omega
  have hfit_core : Fits w (3 + 2 * (inst.n * inst.n) + 4 * inst.n +
      2 * (2 * M) + 2 * inst.eps + 4) :=
    hw.of_le (by unfold EpsInstance.wordBound; nlinarith)
  obtain ⟨y₂, he_core, hb₂, _, hOM₂, _⟩ := core_exec hε hC_le y₁ hb₁ hCM₁ hfit_core
  have hs_eq : auction (fun e => (C_nat e : ℤ)) (inst.eps : ℤ) =
      auction inst.cost (inst.eps : ℤ) := by
    rw [hC_cast]
    exact auction_add_const inst.cost (M : ℤ) (Nat.cast_pos.mpr hε)
  rw [hs_eq] at he_core hOM₂
  obtain ⟨z, he_scat, _, hout_z, hfit_out, _⟩ :=
    exec_scatterOutputCode (auctionInv_auction (Nat.cast_pos.mpr hε))
      (auction_free (Nat.cast_pos.mpr hε)) y₂ hb₂ hOM₂
      (hw.of_le (by unfold EpsInstance.wordBound; nlinarith))
  have hbids_le : (auction inst.cost (inst.eps : ℤ)).bids ≤
      inst.n * (C + inst.eps) / inst.eps + 1 := by
    have hb_raw := bids_auction_le (c := inst.cost) (Nat.cast_pos.mpr hε) hC
    simpa only [bidBound, ← Nat.cast_add, Int.toNat_natCast] using hb_raw
  have hmul_le :
      (auction inst.cost (inst.eps : ℤ)).bids * (28 * inst.n + 30) ≤
        (inst.n * (C + inst.eps) / inst.eps + 1) * (28 * inst.n + 30) :=
    Nat.mul_le_mul_right _ hbids_le
  obtain ⟨t, ht, hex⟩ := he_sf.seq (he_core.seq he_scat)
  have hout_eq : outputList z.mem (z.regs outBase) = inst.assignment := hout_z
  refine ⟨t + 1, hout_eq ▸ hex.executesList outBase (by rwa [hout_eq, inst.length_assignment]), ?_⟩
  unfold epsAuctionTime
  omega

/-- **`Program.ComputesListInTime` form of `executesList_epsAuction` (at `inst.rowSpread`).** -/
theorem computesListInTime_epsAuction :
    epsAuctionProgram.ComputesListInTime (fun _ inst => inst.encode)
      (fun inst _ => epsAuctionTime inst.n inst.rowSpread inst.eps)
      (fun inst w => 0 < inst.eps ∧ Fits w inst.wordBound) EpsInstance.assignment :=
  fun inst _ ⟨hε, hw⟩ _ =>
    executesList_epsAuction inst hε inst.toInstance.sub_le_rowSpread hw

/-- `epsAuctionProgram` does not read the word width (`width%`). -/
theorem not_readsWidth_epsAuctionProgram : ¬ epsAuctionProgram.ReadsWidth := by
  apply Code.not_readsWidth_program
  decide +kernel

/-- `epsAuctionProgram` is deterministic (`rand`-free). -/
theorem isRandFree_epsAuctionProgram : epsAuctionProgram.IsRandFree := by
  rw [epsAuctionProgram, Code.isRandFree_program]
  decide +kernel

/-! ### 4B. Exact `(n + 1)`-scaled integer auction (`O(n³ C + n²)`) -/

private def scaledAuctionCode : Code .standard 26 :=
  .seq (setupAndFillCode true) (.seq coreCode scatterOutputCode)

private def sumScaledCostBody : Code .standard 26 := ram[
  addr ← outBase + one; addr ← addr + idx; val ← *addr;
  addr ← idx * rn; addr ← addr + val; addr ← bC + addr; val2 ← *addr;
  val2 ← val2 / rscale;
  sp ← sp + val2;
  idx ← idx + one ]

private def sumScaledCostTail : Code .standard 26 :=
  .seq (ram[ sp ← #0; idx ← #0 ])
    (.seq (.loop (.lt idx rn) sumScaledCostBody)
      (ram[ val ← rn * rM;
            if sp < val then [
              val2 ← val - sp; sp ← two * val2; sp ← sp + one
            ] else [
              val2 ← sp - val; sp ← two * val2 ] ]))

/-- Standard-basis word-RAM program computing the exact minimum-cost assignment
`Instance.assignment` (`ExecutesList`) via Bertsekas's `(n + 1)`-scaled auction. -/
def scaledAuctionProgram : Program .standard 26 :=
  scaledAuctionCode.program outBase

/-- Standard-basis word-RAM program computing `Instance.encodedMinCost` (`Executes`) via
Bertsekas's `(n + 1)`-scaled auction. -/
def scaledMinCostProgram : Program .standard 26 :=
  (scaledAuctionCode.seq sumScaledCostTail).program sp

/-- Instruction bound `O(n³ C + n²)` for `scaledAuctionProgram` and `scaledMinCostProgram` when `C`
bounds the row cost ranges ([Bertsekas1988], §3). -/
@[expose] def scaledAuctionTime (n C : ℕ) : ℕ :=
  (n * ((n + 1) * C + 1) + 1) * (28 * n + 30) + 22 * (n * n) + 37 * n + 52

private theorem exec_scaledAuctionCode {w : ℕ} (inst : Instance)
    {C : ℕ} (hC : ∀ i j k : Fin inst.n, inst.cost (i, k) - inst.cost (i, j) ≤ (C : ℤ))
    (hw : Fits w inst.wordBound) :
    ∃ z M, ExecWithin w scaledAuctionCode (Data.init inst.encode) z
        (scaledAuctionTime inst.n C - (12 * inst.n + 11)) ∧
      M ≤ inst.maxMag ∧
      (∀ i j : Fin inst.n, (inst.cost (i, j)).natAbs ≤ M) ∧
      BaseRegs inst.n 2 1 (inst.n + 1) M z ∧
      CostMem (2 + inst.n * inst.n)
        (fun p => (inst.n + 1) * (inst.cost p + (M : ℤ)).toNat) z.mem ∧
      outputList z.mem (z.regs outBase) = inst.assignment ∧
      Fits w (z.regs outBase + inst.n) := by
  obtain ⟨y₁, M, he_sf, hM_le, hM_ge, hb₁, hCM₁⟩ :=
    exec_setupAndFillCode (n := inst.n) (eps := 1) true inst.cost inst.encode inst.maxMag
      inst.natAbs_cost_le_maxMag inst.init_mem_n (fun h => by cases h)
      inst.init_mem_cost
      (hw.of_le (by simp only [↓reduceIte]; unfold Instance.wordBound; nlinarith))
  simp only [↓reduceIte] at hb₁ hCM₁
  let C_sc : Fin inst.n × Fin inst.n → ℕ :=
    fun p => (inst.n + 1) * (inst.cost p + (M : ℤ)).toNat
  have hC_sc_le : ∀ i j : Fin inst.n, C_sc (i, j) ≤ 2 * (inst.n + 1) * M := fun i j => by
    have hle2M : (inst.cost (i, j) + (M : ℤ)).toNat ≤ 2 * M := by have := hM_ge i j; omega
    calc (inst.n + 1) * (inst.cost (i, j) + (M : ℤ)).toNat
        ≤ (inst.n + 1) * (2 * M) := Nat.mul_le_mul_left _ hle2M
      _ = 2 * (inst.n + 1) * M := by ring
  have hC_sc_cast :
      (fun e => (C_sc e : ℤ)) =
        fun e => ((inst.n : ℤ) + 1) * inst.cost e + ((inst.n : ℤ) + 1) * (M : ℤ) := by
    funext ⟨i, j⟩
    have hsh : ((inst.cost (i, j) + (M : ℤ)).toNat : ℤ) = inst.cost (i, j) + (M : ℤ) := by
      have := hM_ge i j; omega
    dsimp only [C_sc]
    push_cast
    rw [hsh]
    ring
  have hfit_core : Fits w (2 + 2 * (inst.n * inst.n) + 4 * inst.n +
      2 * (2 * (inst.n + 1) * M) + 2 * 1 + 4) :=
    hw.of_le (by unfold Instance.wordBound; nlinarith)
  obtain ⟨y₂, he_core, hb₂, hCM₂, hOM₂, _⟩ :=
    core_exec Nat.one_pos hC_sc_le y₁ hb₁ hCM₁ hfit_core
  have hs_eq : auction (fun e => (C_sc e : ℤ)) ((1 : ℕ) : ℤ) = scaledAuction inst.cost := by
    rw [hC_sc_cast, Nat.cast_one]
    exact auction_add_const (fun e => ((inst.n : ℤ) + 1) * inst.cost e)
      (((inst.n : ℤ) + 1) * (M : ℤ)) one_pos
  rw [hs_eq] at he_core hOM₂
  have hinv_sc : AuctionInv (fun e => ((inst.n : ℤ) + 1) * inst.cost e) 1
      (scaledAuction inst.cost) := auctionInv_auction one_pos
  have hfree_sc : (scaledAuction inst.cost).free = [] := auction_free one_pos
  obtain ⟨z, he_scat, hbz, hout_z, hfit_out, hf_z⟩ :=
    exec_scatterOutputCode hinv_sc hfree_sc y₂ hb₂ hOM₂
      (hw.of_le (by unfold Instance.wordBound; nlinarith))
  have hCM_z : CostMem (2 + inst.n * inst.n) C_sc z.mem :=
    hCM₂.of_outside fun a ha => hf_z a (by omega)
  have hbids_le : (scaledAuction inst.cost).bids ≤
      inst.n * ((inst.n + 1) * C + 1) + 1 := by
    have hb_raw := bids_scaledAuction_le (c := inst.cost) hC
    have hcast : (((inst.n : ℤ) + 1) * (C : ℤ) + 1).toNat = (inst.n + 1) * C + 1 := by
      exact_mod_cast Int.toNat_natCast ((inst.n + 1) * C + 1)
    rwa [hcast] at hb_raw
  have hmul_le :
      (scaledAuction inst.cost).bids * (28 * inst.n + 30) ≤
        (inst.n * ((inst.n + 1) * C + 1) + 1) * (28 * inst.n + 30) :=
    Nat.mul_le_mul_right _ hbids_le
  refine ⟨z, M, (he_sf.seq (he_core.seq he_scat)).mono ?_,
    hM_le, hM_ge, hbz, hCM_z, hout_z, hfit_out⟩
  unfold scaledAuctionTime
  omega

/-- **`O(n³ C + n²)` Word-RAM exact minimum-cost assignment (`ExecutesList`).** Whenever `C` bounds
every row cost range `inst.cost (i, k) - inst.cost (i, j) ≤ C` and `Fits w inst.wordBound`,
`scaledAuctionProgram` halts within `scaledAuctionTime inst.n C` instructions returning the exact
optimal assignment `inst.assignment` (`sum_scaledAuctionPerm_le`). -/
theorem executesList_scaledAuction {w : ℕ} (inst : Instance)
    {C : ℕ} (hC : ∀ i j k : Fin inst.n, inst.cost (i, k) - inst.cost (i, j) ≤ (C : ℤ))
    (hw : Fits w inst.wordBound) :
    ∃ steps, ExecutesList w scaledAuctionProgram (.init inst.encode) inst.assignment steps ∧
      steps ≤ scaledAuctionTime inst.n C := by
  obtain ⟨z, _, ⟨t, ht, hex⟩, _, _, _, _, hout, hfit⟩ := exec_scaledAuctionCode inst hC hw
  refine ⟨t + 1, hout ▸ hex.executesList outBase (by rwa [hout, inst.length_assignment]), ?_⟩
  unfold scaledAuctionTime at ht ⊢
  omega

/-- **`Program.ComputesListInTime` form of `executesList_scaledAuction` (at `inst.rowSpread`).** -/
theorem computesListInTime_scaledAuction :
    scaledAuctionProgram.ComputesListInTime (fun _ inst => inst.encode)
      (fun inst _ => scaledAuctionTime inst.n inst.rowSpread)
      (fun inst w => Fits w inst.wordBound) Instance.assignment :=
  fun inst _ hw _ => executesList_scaledAuction inst inst.sub_le_rowSpread hw

/-- **`O(n³ C + n²)` Word-RAM exact minimum assignment cost (`Executes`).** -/
theorem executes_scaledMinCost {w : ℕ} (inst : Instance)
    {C : ℕ} (hC : ∀ i j k : Fin inst.n, inst.cost (i, k) - inst.cost (i, j) ≤ (C : ℤ))
    (hw : Fits w inst.wordBound) :
    ∃ steps, Executes w scaledMinCostProgram (.init inst.encode) inst.encodedMinCost steps ∧
      steps ≤ scaledAuctionTime inst.n C := by
  obtain ⟨z, M, he_main, hM_le, hM_ge, hbz, hCMz, hout_z, _⟩ :=
    exec_scaledAuctionCode inst hC hw
  let C_unsc (p : Fin inst.n × Fin inst.n) : ℕ := (inst.cost p + (M : ℤ)).toNat
  have hC_unsc_le : ∀ p : Fin inst.n × Fin inst.n, C_unsc p ≤ 2 * M := by
    rintro ⟨i, j⟩
    have := hM_ge i j
    dsimp only [C_unsc]
    omega
  let π := scaledAuctionPerm inst.cost
  have hmem_out : ∀ i : Fin inst.n,
      z.mem (2 + 2 * (inst.n * inst.n) + 3 * inst.n + 1 + i.val) = (π i).val :=
    fun i => by
      have hi : i.val < (outputList z.mem (z.regs outBase)).length := by
        rw [hout_z, inst.length_assignment]; exact i.isLt
      calc z.mem (2 + 2 * (inst.n * inst.n) + 3 * inst.n + 1 + i.val)
          = z.mem (z.regs outBase + 1 + i.val) := by rw [hbz.houtBase]
        _ = (outputList z.mem (z.regs outBase))[i.val]'hi := (getElem_outputList _ _ _ hi).symm
        _ = inst.assignment[i.val]'(by simp) := by simp [hout_z]
        _ = (π i).val := inst.getElem_assignment i
  have hs₀ : ∃ s₀, ExecWithin w (ram[ sp ← #0; idx ← #0 ] : Code .standard 26) z s₀ 2 ∧
      s₀ = (z.set sp 0).set idx 0 := by
    refine WP.exists_execWithin ?_; wram_exec; rfl
  obtain ⟨s₀, he₀, rfl⟩ := hs₀
  let PS (t : ℕ) (y : Data 26) : Prop :=
    t ≤ inst.n ∧
      (∀ r : Fin 26, r.val < 14 → y.regs r = z.regs r) ∧
      y.mem = z.mem ∧
      y.regs sp = (((List.finRange inst.n).take t).map fun i => C_unsc (i, π i)).sum ∧
      y.regs sp ≤ t * (2 * M)
  have hPS₀ : PS 0 ((z.set sp 0).set idx 0) :=
    ⟨Nat.zero_le _, fun _ _ => by wram_simp, rfl, by wram_simp; simp, by wram_simp; simp⟩
  have hbodyS (y : Data 26) (hy : PS (y.regs idx) y) (hlt : y.regs idx < inst.n) :
      ∃ y', ExecWithin w sumScaledCostBody y y' 10 ∧ PS (y.regs idx + 1) y' ∧
        y'.regs idx = y.regs idx + 1 := by
    obtain ⟨_, hr, hmem, hsp_sum, hsp_le⟩ := hy
    have hby : BaseRegs inst.n 2 1 (inst.n + 1) M y := hbz.of_eq hr
    let i₀ : Fin inst.n := ⟨y.regs idx, hlt⟩
    let j₀ : Fin inst.n := π i₀
    have hj₀_lt := j₀.isLt
    have hload_j :
        y.mem (2 + 2 * (inst.n * inst.n) + 3 * inst.n + 1 + y.regs idx) = j₀.val := by
      rw [hmem]; exact hmem_out i₀
    have hmul_ij : i₀.val * inst.n + j₀.val < inst.n * inst.n :=
      Cslib.Matrix.pairIndex_lt (i₀, j₀)
    have hload_c : y.mem (2 + inst.n * inst.n + (y.regs idx * inst.n + j₀.val)) =
        (inst.n + 1) * C_unsc (i₀, j₀) := by
      rw [hmem]; exact hCMz.hentry i₀ j₀
    have hdiv_sc : ((inst.n + 1) * C_unsc (i₀, j₀)) / (inst.n + 1) = C_unsc (i₀, j₀) :=
      Nat.mul_div_right _ (Nat.succ_pos inst.n)
    have hcu_le : C_unsc (i₀, j₀) ≤ 2 * inst.maxMag :=
      (hC_unsc_le (i₀, j₀)).trans (by omega)
    have hsum_le1 : y.regs sp + C_unsc (i₀, j₀) ≤ (y.regs idx + 1) * (2 * M) := by
      have := hC_unsc_le (i₀, j₀); nlinarith
    have hsum_fit : y.regs sp + C_unsc (i₀, j₀) ≤ 2 * inst.n * inst.maxMag := by
      calc y.regs sp + C_unsc (i₀, j₀) ≤ inst.n * (2 * M) := by nlinarith
        _ ≤ inst.n * (2 * inst.maxMag) := Nat.mul_le_mul_left inst.n (by omega)
        _ = 2 * inst.n * inst.maxMag := by ring
    have hf_o1 : Fits w (2 + 2 * (inst.n * inst.n) + 3 * inst.n + 1) :=
      hw.of_le (by unfold Instance.wordBound; nlinarith)
    have hf_oi : Fits w (2 + 2 * (inst.n * inst.n) + 3 * inst.n + 1 + y.regs idx) :=
      hw.of_le (by unfold Instance.wordBound; nlinarith)
    have hf_in : Fits w (y.regs idx * inst.n) :=
      hw.of_le (by unfold Instance.wordBound; nlinarith)
    have hf_inj : Fits w (y.regs idx * inst.n + j₀.val) :=
      hw.of_le (by unfold Instance.wordBound; nlinarith)
    have hf_bc : Fits w (2 + inst.n * inst.n + (y.regs idx * inst.n + j₀.val)) :=
      hw.of_le (by unfold Instance.wordBound; nlinarith)
    have hf_div : Fits w (C_unsc (i₀, j₀)) :=
      hw.of_le (by unfold Instance.wordBound; nlinarith)
    have hf_acc : Fits w (y.regs sp + C_unsc (i₀, j₀)) :=
      hw.of_le (by unfold Instance.wordBound; nlinarith)
    have hf_i1 : Fits w (y.regs idx + 1) :=
      hw.of_le (by unfold Instance.wordBound; nlinarith)
    refine WP.exists_execWithin ?_
    unfold sumScaledCostBody
    wram_exec [hby.houtBase, hby.hone, hby.hrn, hby.hbC, hby.hrscale,
      hload_j, hload_c, hdiv_sc, hf_o1, hf_oi, hf_in, hf_inj, hf_bc, hf_div, hf_acc, hf_i1]
    refine ⟨⟨by omega, fun r hr' => by wram_simp [hr r hr'], hmem, ?_, ?_⟩, by wram_simp⟩
    · wram_simp [hsp_sum]
      rw [List.take_succ_finRange hlt, List.map_append, List.sum_append, List.map_singleton,
        List.sum_singleton]
    · wram_simp; exact hsum_le1
  obtain ⟨y_sum, hl_sum, hPSn, _⟩ := ExecWithin.loop_count PS
    (fun y hy => (hy.2.1 rn (by decide)).trans hbz.hrn) hbodyS
    (x := (z.set sp 0).set idx 0) (by simp) (by simpa using hPS₀)
  obtain ⟨_, hr_sum, _, hsp_full, hsp_le_n⟩ := hPSn
  have hbs : BaseRegs inst.n 2 1 (inst.n + 1) M y_sum := hbz.of_eq hr_sum
  have hsum_z : (y_sum.regs sp : ℤ) = inst.minCost + (inst.n * M : ℕ) := by
    rw [List.take_of_length_le (by simp), ← Fin.sum_univ_def] at hsp_full
    rw [hsp_full, Nat.cast_sum]
    have hcu_z : ∀ i : Fin inst.n, (C_unsc (i, π i) : ℤ) =
        inst.cost (i, π i) + (M : ℤ) := fun i => by
      have := hM_ge i (π i); dsimp only [C_unsc]; omega
    simp only [hcu_z, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    dsimp only [Instance.minCost]
    push_cast
    ring
  have hf_nM : Fits w (inst.n * M) := by
    have : inst.n * M ≤ inst.n * inst.maxMag := Nat.mul_le_mul_left inst.n hM_le
    exact hw.of_le (by unfold Instance.wordBound; nlinarith)
  have henc_step : ∃ y_end, ExecWithin w
      (ram[ val ← rn * rM;
            if sp < val then [
              val2 ← val - sp; sp ← two * val2; sp ← sp + one
            ] else [
              val2 ← sp - val; sp ← two * val2 ] ] : Code .standard 26) y_sum y_end 6 ∧
      y_end.regs sp = inst.encodedMinCost := by
    refine WP.exists_execWithin ?_
    by_cases hlt_opt : y_sum.regs sp < inst.n * M
    · have hneg_opt : inst.minCost < 0 := by omega
      have hsub_le : y_sum.regs sp ≤ inst.n * M := le_of_lt hlt_opt
      have habs : inst.minCost.natAbs = inst.n * M - y_sum.regs sp := by omega
      have hd_le : inst.n * M - y_sum.regs sp ≤ inst.n * inst.maxMag :=
        (Nat.sub_le _ _).trans (Nat.mul_le_mul_left inst.n hM_le)
      have hf_d : Fits w (inst.n * M - y_sum.regs sp) :=
        hw.of_le (by unfold Instance.wordBound; nlinarith)
      have hf_2d : Fits w (2 * (inst.n * M - y_sum.regs sp)) :=
        hw.of_le (by unfold Instance.wordBound; nlinarith)
      have hf_2d1 : Fits w (2 * (inst.n * M - y_sum.regs sp) + 1) :=
        hw.of_le (by unfold Instance.wordBound; nlinarith)
      wram_exec [hbs.hrn, hbs.hrM, hbs.htwo, hbs.hone, hlt_opt, hsub_le,
        hf_nM, hf_d, hf_2d, hf_2d1]
      wram_simp
      unfold Instance.encodedMinCost Signed.encode
      rw [habs, ite_eq_left hneg_opt]
    · have hnneg_opt : ¬inst.minCost < 0 := by omega
      have hsub_le : inst.n * M ≤ y_sum.regs sp := le_of_not_gt hlt_opt
      have habs : inst.minCost.natAbs = y_sum.regs sp - inst.n * M := by omega
      have hd_le : y_sum.regs sp - inst.n * M ≤ inst.n * (2 * inst.maxMag) :=
        (Nat.sub_le _ _).trans (hsp_le_n.trans (Nat.mul_le_mul_left inst.n (by omega)))
      have hf_d : Fits w (y_sum.regs sp - inst.n * M) :=
        hw.of_le (by unfold Instance.wordBound; nlinarith)
      have hf_2d : Fits w (2 * (y_sum.regs sp - inst.n * M)) :=
        hw.of_le (by unfold Instance.wordBound; nlinarith)
      wram_exec [hbs.hrn, hbs.hrM, hbs.htwo, hbs.hone, hlt_opt, hsub_le,
        hf_nM, hf_d, hf_2d]
      wram_simp
      unfold Instance.encodedMinCost Signed.encode
      rw [habs, ite_eq_right hnneg_opt, Nat.add_zero]
  obtain ⟨y_end, he_enc, hsp_end⟩ := henc_step
  have he_tail : ExecWithin w sumScaledCostTail z y_end (12 * inst.n + 10) :=
    (he₀.seq (hl_sum.seq he_enc)).mono (by simp; omega)
  obtain ⟨t, ht, hex⟩ := he_main.seq he_tail
  refine ⟨t + 1, hsp_end ▸ hex.executes sp, ?_⟩
  unfold scaledAuctionTime at ht ⊢
  omega

/-- **`Program.ComputesInTime` form of `executes_scaledMinCost` (at `inst.rowSpread`).** -/
theorem computesInTime_scaledMinCost :
    scaledMinCostProgram.ComputesInTime (fun _ inst => inst.encode)
      (fun inst _ => scaledAuctionTime inst.n inst.rowSpread)
      (fun inst w => Fits w inst.wordBound) Instance.encodedMinCost :=
  fun inst _ hw _ => executes_scaledMinCost inst inst.sub_le_rowSpread hw

/-- `scaledAuctionProgram` does not read the word width (`width%`). -/
theorem not_readsWidth_scaledAuctionProgram : ¬ scaledAuctionProgram.ReadsWidth := by
  apply Code.not_readsWidth_program
  decide +kernel

/-- `scaledAuctionProgram` is deterministic (`rand`-free). -/
theorem isRandFree_scaledAuctionProgram : scaledAuctionProgram.IsRandFree := by
  rw [scaledAuctionProgram, Code.isRandFree_program]
  decide +kernel

/-- `scaledMinCostProgram` does not read the word width (`width%`). -/
theorem not_readsWidth_scaledMinCostProgram : ¬ scaledMinCostProgram.ReadsWidth := by
  apply Code.not_readsWidth_program
  decide +kernel

/-- `scaledMinCostProgram` is deterministic (`rand`-free). -/
theorem isRandFree_scaledMinCostProgram : scaledMinCostProgram.IsRandFree := by
  rw [scaledMinCostProgram, Code.isRandFree_program]
  decide +kernel

end Cslib.Algorithms.WordRAM.Auction
