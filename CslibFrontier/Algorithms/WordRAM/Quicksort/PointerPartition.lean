/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.Quicksort
public import CslibFrontier.Algorithms.WordRAM.Quicksort.PointerPivot
public import CslibFrontier.Algorithms.WordRAM.Quicksort.LocalStack
public import CslibFrontier.Computability.WordRAM.PointerMachine.Local
public import CslibFrontier.Algorithms.WordRAM.Quicksort.LocalModel
import CslibFrontier.Computability.WordRAM.SymbolicExec

/-!
# Local-address three-way quicksort partition

Three held addresses delimit the partition zones. The loop exits when the scan cursor
and the upper cursor meet. Payload swaps use only the held addresses.

## Main results

* `localPartition_exec`: partition invariant and charged cost for the local-address loop.
* `pointerPartition_exec`: the same guarantee after compiling to pointer-machine code.
* `localPartitionFromPivot_exec`: initialization and loop from a held range and a pivot key.
* `partitionAtRank_exec`: countdown pivot selection and partition at a supplied rank.
-/

public section

namespace Cslib.Algorithms.WordRAM.Quicksort

open Cslib.WordRAM Reg

private abbrev partModel := localModel

private abbrev PartCode := Program.Code (Local.Op partModel 16 16) (Local.Test partModel 16 16)

private def localSwap (a b : Fin 16) : PartCode :=
  .seq (.op (.loadData val a)) (.seq (.op (.loadData val2 b))
    (.seq (.op (.storeData a val2)) (.op (.storeData b val))))

private def localPartStep : PartCode :=
  .seq (.op (.loadData val cur))
    (.branch (.scalar () val piv)
      (.seq (localSwap lt cur) (.seq (.op (.move .next lt lt)) (.op (.move .next cur cur))))
      (.branch (.scalar () piv val)
        (.seq (.op (.move .prev gt gt)) (localSwap cur gt))
        (.op (.move .next cur cur))))

/-- Structured local-address three-way partition loop. -/
def localPartition : Program.Code (Local.Op localModel 16 16)
    (Local.Test localModel 16 16) :=
  .loopUntil (.addrEq cur gt) localPartStep

private def isAddressReg (r : Fin 16) : Bool := r == lo || r == hi || r == lt || r == cur || r == gt

private abbrev LocalData (n : ℕ) := Local.Data partModel n 16 16

/-- Observe the local partition state as a WordRAM state. Null cursors and cells past the
allocated interval are assigned an observation for use in the numeric invariant. -/
def partitionView {n : ℕ} (x : Local.Data localModel n 16 16) : Data 16 :=
  ⟨fun r => if isAddressReg r then ((x.addr r).map Fin.val).getD n else x.scalars r,
    fun a => if h : a < n then x.values ⟨a, h⟩ else 0⟩

/-- The numeric observation reads exactly the payload of every allocated cell. -/
theorem partitionView_mem {n : ℕ} (x : Local.Data localModel n 16 16) (a : Fin n) :
    (partitionView x).mem a.val = x.values a := by
  simp [partitionView, a.isLt]

/-- The memory observation depends only on payloads. -/
theorem partitionView_mem_congr {n : ℕ} {x y : Local.Data localModel n 16 16}
    (h : x.values = y.values) : (partitionView x).mem = (partitionView y).mem := by
  simp only [partitionView, h]

/-- Registers zero and one are scalar registers in the numeric partition observation. -/
theorem partitionView_one {n : ℕ} (x : Local.Data localModel n 16 16) :
    (partitionView x).regs one = x.scalars one := by
  simp [partitionView, isAddressReg]

private theorem cursor_lookup {n : ℕ} (x : LocalData n) {r : Fin 16} (hr : isAddressReg r = true)
    (h : (partitionView x).regs r < n) :
    x.addr r = some ⟨(partitionView x).regs r, h⟩ := by
  change (if isAddressReg r then ((x.addr r).map Fin.val).getD n else x.scalars r) < n at h
  cases ha : x.addr r with
  | none => simp [ha, hr] at h
  | some a => simp [partitionView, ha, hr]

private theorem view_setScalar {n : ℕ} (x : LocalData n) {r : Fin 16} (hr : isAddressReg r = false)
    (v : ℕ) :
    partitionView { x with scalars := Function.update x.scalars r v } =
      (partitionView x).set r v := by
  apply Data.ext
  · funext j
    by_cases h : j = r
    · subst j
      simp [partitionView, hr]
    · simp [partitionView, h]
  · rfl

private theorem view_setCursor {n : ℕ} (x : LocalData n) {r : Fin 16} (hr : isAddressReg r = true)
    (a : Fin n) :
    partitionView { x with addr := Function.update x.addr r (some a) } =
      (partitionView x).set r a.val := by
  apply Data.ext
  · funext j
    by_cases h : j = r
    · subst j
      simp [partitionView, hr]
    · simp [partitionView, h]
  · rfl

private theorem view_load {n : ℕ} (x : LocalData n) {r a : Fin 16} (hr : isAddressReg r = false)
    (ha : isAddressReg a = true) (h : (partitionView x).regs a < n) :
    partitionView ((Local.Op.loadData r a).eval x) =
      (partitionView x).set r ((partitionView x).mem ((partitionView x).regs a)) := by
  have hh := cursor_lookup x ha h
  simp only [Local.Op.eval, hh, Option.elim, view_setScalar x hr]
  congr 1
  change x.values ⟨(partitionView x).regs a, h⟩ =
    (if h' : (partitionView x).regs a < n then x.values ⟨(partitionView x).regs a, h'⟩ else 0)
  simp only [dite_eq_left h]

private theorem view_store {n : ℕ} (x : LocalData n) {a r : Fin 16} (ha : isAddressReg a = true)
    (hr : isAddressReg r = false) (h : (partitionView x).regs a < n) :
    partitionView ((Local.Op.storeData a r).eval x) =
      (partitionView x).write ((partitionView x).regs a) ((partitionView x).regs r) := by
  have hh := cursor_lookup x ha h
  simp only [Local.Op.eval, hh, Option.elim]
  refine Data.ext ?_ ?_
  · rfl
  funext j
  have hs : (partitionView x).regs r = x.scalars r := by simp [partitionView, hr]
  change (if hjn : j < n then
      Function.update x.values ⟨(partitionView x).regs a, h⟩ (x.scalars r) ⟨j, hjn⟩ else 0) =
    Function.update (partitionView x).mem ((partitionView x).regs a) ((partitionView x).regs r) j
  rw [hs]
  by_cases hj : j = (partitionView x).regs a
  · subst j
    simp only [dite_eq_left h, Function.update_self]
  · rw [Function.update_of_ne hj]
    change (if hjn : j < n then
        Function.update x.values ⟨(partitionView x).regs a, h⟩ (x.scalars r) ⟨j, hjn⟩ else 0) =
      (if hjn : j < n then x.values ⟨j, hjn⟩ else 0)
    split
    · rename_i hjn
      simp only [Function.update_of_ne
        (fun he : (⟨j, hjn⟩ : Fin n) = ⟨(partitionView x).regs a, h⟩ => hj (congrArg Fin.val he))]
    · rfl

private theorem view_next {n : ℕ} (x : LocalData n) {r : Fin 16} (hr : isAddressReg r = true)
    (h : (partitionView x).regs r + 1 < n) :
    partitionView ((Local.Op.move .next r r).eval x) =
      (partitionView x).set r ((partitionView x).regs r + 1) := by
  have hp : (partitionView x).regs r < n := by omega
  simp [Local.Op.eval, cursor_lookup x hr hp, Local.Direction.move, h, view_setCursor x hr]

private theorem view_prev {n : ℕ} (x : LocalData n) {r : Fin 16} (hr : isAddressReg r = true)
    (h : (partitionView x).regs r < n) (hp : 0 < (partitionView x).regs r) :
    partitionView ((Local.Op.move .prev r r).eval x) =
      (partitionView x).set r ((partitionView x).regs r - 1) := by
  simp [Local.Op.eval, cursor_lookup x hr h, Local.Direction.move, Nat.ne_of_gt hp,
    view_setCursor x hr]

private def swapEffect {n : ℕ} (a b : Fin 16) (x : LocalData n) : LocalData n :=
  ((Local.Op.storeData b val).eval
    ((Local.Op.storeData a val2).eval
      ((Local.Op.loadData val2 b).eval ((Local.Op.loadData val a).eval x))))

private theorem swap_exec {n : ℕ} (a b : Fin 16) (x : LocalData n) :
    Program.Exec (Local.instructionSet partModel n 16 16) (localSwap a b) x (swapEffect a b x) 4 :=
  .seq (.op rfl) (.seq (.op rfl) (.seq (.op rfl) (.op rfl)))

private theorem view_swap {n : ℕ} (x : LocalData n) {a b : Fin 16}
    (ha : isAddressReg a = true) (hb : isAddressReg b = true)
    (hva : (partitionView x).regs a < n) (hvb : (partitionView x).regs b < n) :
    partitionView (swapEffect a b x) =
      ⟨Function.update (Function.update (partitionView x).regs val
        ((partitionView x).mem ((partitionView x).regs a))) val2
        ((partitionView x).mem ((partitionView x).regs b)),
        swapMem (partitionView x).mem ((partitionView x).regs a) ((partitionView x).regs b)⟩ := by
  have hna : a ≠ val := by intro h; subst a; contradiction
  have hnb : b ≠ val := by intro h; subst b; contradiction
  have hna' : a ≠ val2 := by intro h; subst a; contradiction
  have hnb' : b ≠ val2 := by intro h; subst b; contradiction
  let a₁ := (Local.Op.loadData val a).eval x
  let a₂ := (Local.Op.loadData val2 b).eval a₁
  let a₃ := (Local.Op.storeData a val2).eval a₂
  have h₁ := view_load x (r := val) (by decide) ha hva
  have h₂ := view_load a₁ (r := val2) (by decide) hb (by rw [h₁]; simpa [hnb])
  have h₃ := view_store a₂ (r := val2) ha (by decide) (by rw [h₂, h₁]; simpa [hna, hna'])
  have h₄ := view_store a₃ (r := val) hb (by decide) (by
    rw [h₃, h₂, h₁]
    simpa [hnb, hnb'])
  change partitionView ((Local.Op.storeData b val).eval a₃) = _
  rw [h₄, h₃, h₂, h₁]
  simp [Data.write, Data.set, hna, hnb, hna', hnb', swapMem]

private theorem view_lt {n : ℕ} (x : LocalData n) {a b : Fin 16}
    (ha : isAddressReg a = false) (hb : isAddressReg b = false) :
    (Local.instructionSet partModel n 16 16).Holds (.scalar () a b) x ↔
      (partitionView x).regs a < (partitionView x).regs b := by
  change decide (x.scalars a < x.scalars b) = true ↔ _
  simp [partitionView, ha, hb]

private theorem localStep_refines {n w vlo vhi vpiv : ℕ} {mem₀ : ℕ → ℕ}
    (x : LocalData n) (hI : PartInv w vlo vhi vpiv mem₀ (partitionView x))
    (hcg : (partitionView x).regs cur < (partitionView x).regs gt) (hbound : vhi < n) :
    ∃ z t, Program.Exec (Local.instructionSet partModel n 16 16) localPartStep x z t ∧
      Exec w partStep (partitionView x) (partitionView z) t := by
  let s := partitionView x
  change s.regs cur < s.regs gt at hcg
  change PartInv w vlo vhi vpiv mem₀ s at hI
  have hcur : s.regs cur < n := by have := hI.gt_le_hi; omega
  have hlt : s.regs lt < n := by have := hI.lt_le_cur; omega
  have hgt : s.regs gt < n := by have := hI.gt_le_hi; omega
  have hgtpos : 0 < s.regs gt := by omega
  have hcur' : s.regs cur + 1 < n := by omega
  have hlt' : s.regs lt + 1 < n := by have := hI.lt_le_cur; omega
  let x₁ := (Local.Op.loadData val cur).eval x
  have hv₁ := view_load x (r := val) (by decide) (by decide) hcur
  have hload : Program.Exec (Local.instructionSet partModel n 16 16)
      (.op (.loadData val cur)) x x₁ 1 := .op rfl
  have hv₁' : partitionView x₁ = s.set val (s.mem (s.regs cur)) := hv₁
  have hfit (v : ℕ) (hv : v ≤ vhi) : Fits w v := hI.fits_hi.of_le hv
  have hltcur := hI.lt_le_cur
  have hgthi := hI.gt_le_hi
  by_cases hltp : s.mem (s.regs cur) < vpiv
  · let x₂ := swapEffect lt cur x₁
    let x₃ := (Local.Op.move .next lt lt).eval x₂
    let z := (Local.Op.move .next cur cur).eval x₃
    have hs₂ := view_swap x₁ (a := lt) (b := cur) (by decide) (by decide)
      (by rw [hv₁']; simpa using hlt) (by rw [hv₁']; simpa using hcur)
    have hs₃ := view_next x₂ (r := lt) (by decide) (by
      change (partitionView (swapEffect lt cur x₁)).regs lt + 1 < n
      rw [hs₂, hv₁']; simpa using hlt')
    have hsz := view_next x₃ (r := cur) (by decide) (by
      change (partitionView ((Local.Op.move .next lt lt).eval x₂)).regs cur + 1 < n
      rw [hs₃, hs₂, hv₁']; simpa using hcur')
    have hpos : (Local.instructionSet partModel n 16 16).Holds (.scalar () val piv) x₁ := by
      rw [view_lt x₁ (by decide) (by decide), hv₁']
      simpa [s, hI.piv_eq] using hltp
    refine ⟨z, 8, .seq hload (.branch_pos hpos (.seq (swap_exec lt cur x₁)
      (.seq (.op rfl) (.op rfl)))), ?_⟩
    change Exec w partStep s (partitionView ((Local.Op.move .next cur cur).eval x₃)) 8
    rw [hsz, hs₃, hs₂, hv₁']
    apply WP.Exact.exec
    unfold partStep swapCells
    wram_exec [hI.piv_eq, hI.one_eq, hfit, hltp, s]
    rfl
  · have hneg : ¬(Local.instructionSet partModel n 16 16).Holds (.scalar () val piv) x₁ := by
      rw [view_lt x₁ (by decide) (by decide), hv₁']
      simpa [s, hI.piv_eq] using hltp
    by_cases hgtp : vpiv < s.mem (s.regs cur)
    · let x₂ := (Local.Op.move .prev gt gt).eval x₁
      let z := swapEffect cur gt x₂
      have hs₂ := view_prev x₁ (r := gt) (by decide)
        (by rw [hv₁']; simpa using hgt) (by rw [hv₁']; simpa using hgtpos)
      have hsz := view_swap x₂ (a := cur) (b := gt) (by decide) (by decide)
        (by dsimp [x₂]; rw [hs₂, hv₁']; simpa using hcur)
        (by dsimp [x₂]; rw [hs₂, hv₁']; simpa using Nat.lt_of_le_of_lt (Nat.sub_le _ _) hgt)
      have hpos : (Local.instructionSet partModel n 16 16).Holds (.scalar () piv val) x₁ := by
        rw [view_lt x₁ (by decide) (by decide), hv₁']
        simpa [s, hI.piv_eq] using hgtp
      refine ⟨z, 9, .seq hload (.branch_neg hneg (.branch_pos hpos
        (.seq (.op rfl) (swap_exec cur gt x₂)))), ?_⟩
      change Exec w partStep s (partitionView (swapEffect cur gt x₂)) 9
      rw [hsz]
      dsimp [x₂]
      rw [hs₂, hv₁']
      apply WP.Exact.exec
      unfold partStep swapCells
      wram_exec [hI.piv_eq, hI.one_eq, hfit, hltp, hgtp, s]
      rfl
    · let z := (Local.Op.move .next cur cur).eval x₁
      have hsz := view_next x₁ (r := cur) (by decide) (by rw [hv₁']; simpa using hcur')
      have hneg' : ¬(Local.instructionSet partModel n 16 16).Holds (.scalar () piv val) x₁ := by
        rw [view_lt x₁ (by decide) (by decide), hv₁']
        simpa [s, hI.piv_eq] using hgtp
      refine ⟨z, 6, .seq hload (.branch_neg hneg (.branch_neg hneg' (.op rfl))), ?_⟩
      change Exec w partStep s (partitionView ((Local.Op.move .next cur cur).eval x₁)) 6
      rw [hsz, hv₁']
      apply WP.Exact.exec
      unfold partStep swapCells
      wram_exec [hI.piv_eq, hI.one_eq, hfit, hltp, hgtp, s]
      rfl

private theorem cursors_meet {n : ℕ} (x : LocalData n)
    (hc : (partitionView x).regs cur < n) (hg : (partitionView x).regs gt < n) :
    (Local.instructionSet partModel n 16 16).Holds (.addrEq cur gt) x ↔
      (partitionView x).regs cur = (partitionView x).regs gt := by
  change x.addr cur = x.addr gt ↔ _
  rw [cursor_lookup x (r := cur) (by decide) hc, cursor_lookup x (r := gt) (by decide) hg]
  simp [Fin.ext_iff]

/-- The local-address three-way partition preserves the WordRAM partition invariant, and finishes
when the scan and upper cursors meet. The exclusive endpoint has an allocated record, so all
three cursors remain nonnull throughout the scan. -/
theorem localPartition_exec {n w vlo vhi vpiv : ℕ}
    (x : Local.Data localModel n 16 16)
    (hI : PartInv w vlo vhi vpiv (partitionView x).mem (partitionView x))
    (hcur : (partitionView x).regs cur = vlo) (hgt : (partitionView x).regs gt = vhi)
    (hbound : vhi < n) :
    ∃ y : Local.Data localModel n 16 16,
      Program.ExecWithin (Local.instructionSet localModel n 16 16)
        localPartition x y (11 * (vhi - vlo) + 1) ∧
      PartInv w vlo vhi vpiv (partitionView x).mem (partitionView y) ∧
      (partitionView y).regs cur = (partitionView y).regs gt := by
  let P (z : LocalData n) := PartInv w vlo vhi vpiv (partitionView x).mem (partitionView z)
  let remaining (z : LocalData n) := (partitionView z).regs gt - (partitionView z).regs cur
  have meet (z : LocalData n) (hz : P z) :
      (Local.instructionSet partModel n 16 16).Holds (.addrEq cur gt) z ↔
        (partitionView z).regs cur = (partitionView z).regs gt :=
    cursors_meet z ((hz.cur_le_gt.trans hz.gt_le_hi).trans_lt hbound)
      (hz.gt_le_hi.trans_lt hbound)
  obtain ⟨y, hrun, hy, hend⟩ := Program.ExecWithin.loopUntil_invariant
    (I := Local.instructionSet partModel n 16 16) (t := .addrEq cur gt)
    (body := localPartStep) P remaining (T := 9) (by
      intro z hz hn
      have hlt : (partitionView z).regs cur < (partitionView z).regs gt :=
        lt_of_le_of_ne hz.cur_le_gt fun he => hn ((meet z hz).2 he)
      obtain ⟨a, time, hlocal, hword⟩ := localStep_refines z hz hlt hbound
      obtain ⟨b, ⟨t, hcost, hstep⟩, hb, hrem⟩ := partStep_spec hz hlt
      obtain ⟨rfl, rfl⟩ := hword.unique hstep
      exact ⟨a, ⟨time, hcost, hlocal⟩, hb, hrem⟩) hI
  obtain ⟨t, ht, he⟩ := hrun
  have hcost : t ≤ 11 * (vhi - vlo) + 1 := by
    simpa [remaining, hcur, hgt, Nat.mul_comm] using ht
  exact ⟨y, ⟨t, hcost, he⟩, hy, (meet y hy).1 hend⟩

/-- The pointer-machine implementation inherits the partition invariant and linear cost. -/
theorem pointerPartition_exec {n w vlo vhi vpiv : ℕ}
    (x : Local.Data localModel n 16 16)
    (hI : PartInv w vlo vhi vpiv (partitionView x).mem (partitionView x))
    (hcur : (partitionView x).regs cur = vlo) (hgt : (partitionView x).regs gt = vhi)
    (hbound : vhi < n) :
    ∃ y : Local.Data localModel n 16 16,
      Cslib.PointerMachine.ExecWithin (Local.compile localPartition) (Local.encode x)
        (Local.encode y) (11 * (vhi - vlo) + 1) ∧
      PartInv w vlo vhi vpiv (partitionView x).mem (partitionView y) ∧
      (partitionView y).regs cur = (partitionView y).regs gt := by
  obtain ⟨y, ⟨t, ht, he⟩, hy, hend⟩ := localPartition_exec x hI hcur hgt hbound
  exact ⟨y, ⟨t, ht, Local.exec_compile he⟩, hy, hend⟩

private def initPartition : PartCode :=
  .seq (.op (.copyAddr lt lo)) (.seq (.op (.copyAddr cur lo)) (.op (.copyAddr gt hi)))

/-- Set up the three cursors from the held endpoints, then partition around the key in `piv`. -/
def localPartitionFromPivot : Program.Code (Local.Op localModel 16 16)
    (Local.Test localModel 16 16) :=
  .seq initPartition localPartition

private theorem partition_frame {n t : ℕ} {x y : LocalData n}
    (h : Program.Exec (Local.instructionSet partModel n 16 16) localPartitionFromPivot x y t) :
    y.addr sp = x.addr sp ∧ y.addr stackHi = x.addr stackHi ∧
      y.scalars zero = x.scalars zero ∧ y.refs = x.refs := by
  refine h.invariant_ops
    (fun z : LocalData n =>
      z.addr sp = x.addr sp ∧ z.addr stackHi = x.addr stackHi ∧
        z.scalars zero = x.scalars zero ∧ z.refs = x.refs)
    ?_ ⟨rfl, rfl, rfl, rfl⟩
  intro o ho a b he hab
  change some (o.eval a) = some b at he
  obtain rfl := Option.some.inj he
  simp only [localPartitionFromPivot, initPartition, localPartition, localPartStep, localSwap,
    Program.Code.ops, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl <;>
    first
    | simpa [Local.Op.eval] using hab
    | simp only [Local.Op.eval, Option.elim]
      split <;> simpa using hab

/-- A held range and pivot key suffice to initialize and run the verified partition. -/
theorem localPartitionFromPivot_exec {n w : ℕ}
    (x : Local.Data localModel n 16 16)
    (start stop : Fin n) (hlo : x.addr lo = some start) (hhi : x.addr hi = some stop)
    (horder : start.val ≤ stop.val) (hfit : Fits w stop.val) (hone : x.scalars one = 1) :
    ∃ y : Local.Data localModel n 16 16,
      Program.ExecWithin (Local.instructionSet localModel n 16 16)
        localPartitionFromPivot x y (11 * (stop.val - start.val) + 4) ∧
      PartInv w start.val stop.val (x.scalars piv) (partitionView x).mem (partitionView y) ∧
      (partitionView y).regs cur = (partitionView y).regs gt := by
  let x₁ := (Local.Op.copyAddr lt lo).eval x
  let x₂ := (Local.Op.copyAddr cur lo).eval x₁
  let x₃ := (Local.Op.copyAddr gt hi).eval x₂
  have hinit : Program.Exec (Local.instructionSet partModel n 16 16) initPartition x x₃ 3 :=
    .seq (.op rfl) (.seq (.op rfl) (.op rfl))
  have h₁ : partitionView x₁ = (partitionView x).set lt start.val := by
    simpa [x₁, Local.Op.eval, hlo] using view_setCursor x (r := lt) (by decide) start
  have h₂ : partitionView x₂ = (partitionView x₁).set cur start.val := by
    have hsource : x₁.addr lo = some start := by simpa [x₁, Local.Op.eval] using hlo
    simpa [x₂, Local.Op.eval, hsource] using view_setCursor x₁ (r := cur) (by decide) start
  have h₃ : partitionView x₃ = (partitionView x₂).set gt stop.val := by
    have hsource : x₂.addr hi = some stop := by simpa [x₂, x₁, Local.Op.eval] using hhi
    simpa [x₃, Local.Op.eval, hsource] using view_setCursor x₂ (r := gt) (by decide) stop
  have hview : partitionView x₃ =
      (((partitionView x).set lt start.val).set cur start.val).set gt stop.val := by
    rw [h₃, h₂, h₁]
  have hmem : (partitionView x₃).mem = (partitionView x).mem := by rw [hview]; rfl
  have hfirst : (partitionView x₃).regs cur = start.val := by rw [hview]; simp
  have hlast : (partitionView x₃).regs gt = stop.val := by rw [hview]; simp
  have hinv : PartInv w start.val stop.val (x.scalars piv)
      (partitionView x₃).mem (partitionView x₃) := by
    rw [hview]
    refine ⟨?_, ?_, ?_, ?_, hfit, ?_, ?_, ?_, ?_, .refl _, Modifies.refl _ _, ?_, ?_, ?_⟩
    all_goals simp [partitionView, isAddressReg, hlo, hhi, hone, horder]
    all_goals omega
  obtain ⟨y, hy, hyInv, hend⟩ := localPartition_exec x₃ hinv hfirst hlast stop.isLt
  refine ⟨y, ?_, hmem ▸ hyInv, hend⟩
  exact (Program.ExecWithin.seq ⟨3, le_rfl, hinit⟩ hy).mono (by omega)

/-- Read the pivot at the rank in `tmp`, then partition the held range. -/
def partitionAtRank : Program.Code (Local.Op localModel 16 16)
    (Local.Test localModel 16 16) :=
  .seq (.op (.copyAddr cur lo))
    (.seq (pivotWalk cur tmp zero one piv) localPartitionFromPivot)

/-- The countdown and partition share the existing WordRAM invariant. A supplied rank strictly
inside the range costs at most `11 * length + 4 * rank + 8` instructions. -/
theorem partitionAtRank_exec {n w : ℕ} (x : Local.Data localModel n 16 16)
    (start stop : Fin n) (rank : ℕ)
    (hlo : x.addr lo = some start) (hhi : x.addr hi = some stop)
    (hoffset : x.scalars tmp = rank) (hzero : x.scalars zero = 0) (hone : x.scalars one = 1)
    (hrank : start.val + rank < stop.val) (hfit : Fits w stop.val) :
    ∃ y : Local.Data localModel n 16 16,
      Program.ExecWithin (Local.instructionSet localModel n 16 16)
        partitionAtRank x y (11 * (stop.val - start.val) + 4 * rank + 8) ∧
      PartInv w start.val stop.val (x.values ⟨start.val + rank, hrank.trans stop.isLt⟩)
        (partitionView x).mem (partitionView y) ∧
      (partitionView y).regs cur = (partitionView y).regs gt ∧
      y.addr sp = x.addr sp ∧ y.addr stackHi = x.addr stackHi ∧
      y.scalars zero = x.scalars zero ∧ y.refs = x.refs := by
  let a : Fin n := ⟨start.val + rank, hrank.trans stop.isLt⟩
  let x₁ := (Local.Op.copyAddr cur lo).eval x
  let x₂ := { x₁ with
    addr := Function.update x₁.addr cur (some a)
    scalars := Function.update (Function.update x₁.scalars tmp 0) piv (x₁.values a) }
  have hcopy : Program.Exec (Local.instructionSet partModel n 16 16)
      (.op (.copyAddr cur lo)) x x₁ 1 := .op rfl
  have hcur : x₁.addr cur = some start := by simp [x₁, Local.Op.eval, hlo]
  have hpivot : Program.ExecWithin (Local.instructionSet partModel n 16 16)
      (pivotWalk cur tmp zero one piv) x₁ x₂ (4 * rank + 3) :=
    pivotWalk_exec cur tmp zero one piv (by decide) (by decide) x₁ start rank
      hcur hoffset hzero hone (hrank.trans stop.isLt)
  have hlo₂ : x₂.addr lo = some start := by simp [x₂, x₁, Local.Op.eval, hlo]
  have hhi₂ : x₂.addr hi = some stop := by simpa [x₂, x₁, Local.Op.eval] using hhi
  have hone₂ : x₂.scalars one = 1 := by simpa [x₂, x₁, Local.Op.eval] using hone
  have horder : start.val ≤ stop.val := by omega
  obtain ⟨y, hpart, hy, hend⟩ := localPartitionFromPivot_exec x₂ start stop
    hlo₂ hhi₂ horder hfit hone₂
  have hpiv₂ : x₂.scalars piv = x.values a := by simp [x₂, x₁, Local.Op.eval]
  have hmem₂ : (partitionView x₂).mem = (partitionView x).mem := rfl
  have hframe : y.addr sp = x₂.addr sp ∧ y.addr stackHi = x₂.addr stackHi ∧
      y.scalars zero = x₂.scalars zero ∧ y.refs = x₂.refs := by
    obtain ⟨_, _, he⟩ := hpart
    exact partition_frame he
  refine ⟨y, ?_, ?_, hend, ?_⟩
  · exact (Program.ExecWithin.seq ⟨1, le_rfl, hcopy⟩
      (Program.ExecWithin.seq hpivot hpart)).mono (by omega)
  · rwa [hpiv₂, hmem₂] at hy
  · simpa [x₂, x₁, Local.Op.eval] using hframe

private def countChildren : PartCode :=
  .seq (localRangeLength lo lt) (.seq (.op (.copyData val tmp)) (localRangeLength gt hi))

private def pushLargerFirst : PartCode :=
  .branch (.scalar () val tmp)
    (.seq (localEnqueue gt hi) (localEnqueue lo lt))
    (.seq (localEnqueue lo lt) (localEnqueue gt hi))

/-- Partition at the supplied pivot rank and put the smaller nontrivial child on top. -/
def partitionAndEnqueue : Program.Code (Local.Op localModel 16 16)
    (Local.Test localModel 16 16) :=
  .seq partitionAtRank (.seq countChildren pushLargerFirst)

/-- Once given the sampled rank, the entire partition and scheduling phase is deterministic. -/
theorem partitionAndEnqueue_noDraw : NoDraw partitionAndEnqueue := by
  have hp := pivotWalk_noDraw cur tmp zero one piv
  have hl := localEnqueue_noDraw lo lt
  have hr := localEnqueue_noDraw gt hi
  have hlenl := localRangeLength_noDraw lo lt
  have hlenr := localRangeLength_noDraw gt hi
  intro dst a b hm
  simp [partitionAndEnqueue, partitionAtRank, localPartitionFromPivot, initPartition,
    localPartition, localPartStep, localSwap, countChildren, pushLargerFirst,
    hp dst a b, hl dst a b, hr dst a b, hlenl dst a b, hlenr dst a b] at hm

/-- The scratch state after recording the child lengths. -/
@[expose] def countedChildren {n : ℕ} (x : Local.Data localModel n 16 16)
    (start left right stop : Fin n) : Local.Data localModel n 16 16 :=
  { x with
    addr := Function.update x.addr stackLo (some stop)
    scalars := Function.update (Function.update x.scalars val (left.val - start.val))
      tmp (stop.val - right.val) }

/-- The state after the two children have been measured and pushed in decreasing size order. -/
@[expose] def scheduledChildren {n : ℕ} (x : Local.Data localModel n 16 16)
    (start left right stop slot : Fin n) (hroom : slot.val + 4 < n) :
    Local.Data localModel n 16 16 :=
  let z := countedChildren x start left right stop
  if left.val - start.val < stop.val - right.val then
    enqueuePairState z right stop start left slot hroom
  else enqueuePairState z start left right stop slot hroom

private theorem countChildren_exec {n : ℕ} (x : LocalData n) (start left right stop : Fin n)
    (hlo : x.addr lo = some start) (hlt : x.addr lt = some left)
    (hgt : x.addr gt = some right) (hhi : x.addr hi = some stop)
    (h₁ : start.val ≤ left.val) (h₂ : right.val ≤ stop.val)
    (hzero : x.scalars zero = 0) (hone : x.scalars one = 1) :
    Program.ExecWithin (Local.instructionSet localModel n 16 16)
      countChildren x (countedChildren x start left right stop)
        (4 * (left.val - start.val) + 4 * (stop.val - right.val) + 7) := by
  let u := { x with
    addr := Function.update x.addr stackLo (some left)
    scalars := Function.update x.scalars tmp (left.val - start.val) }
  let v := (Local.Op.copyData val tmp).eval u
  have he₁ : Program.ExecWithin (Local.instructionSet localModel n 16 16)
      (localRangeLength lo lt) x u (4 * (left.val - start.val) + 3) :=
    ⟨_, le_rfl, localRangeLength_exec lo lt (by decide) x start left hlo hlt h₁ hzero hone⟩
  have hc : Program.Exec (Local.instructionSet localModel n 16 16)
      (.op (.copyData val tmp)) u v 1 := .op rfl
  have he₂ := localRangeLength_exec gt hi (by decide) v right stop
    (by simpa [v, u, Local.Op.eval] using hgt)
    (by simpa [v, u, Local.Op.eval] using hhi) h₂
    (by simpa [v, u, Local.Op.eval] using hzero) (by simpa [v, u, Local.Op.eval] using hone)
  have he₂' : Program.ExecWithin (Local.instructionSet localModel n 16 16)
      (localRangeLength gt hi) v (countedChildren x start left right stop)
      (4 * (stop.val - right.val) + 3) := by
    refine ⟨_, le_rfl, ?_⟩
    simpa [countedChildren, v, u, Local.Op.eval,
      Function.update_comm (show tmp ≠ val by decide), Function.update_idem] using he₂
  exact (Program.ExecWithin.seq he₁ (Program.ExecWithin.seq ⟨1, le_rfl, hc⟩ he₂')).mono
    (by omega)

private theorem schedule_exec {n : ℕ} (x : LocalData n) (start left right stop slot : Fin n)
    (hlo : x.addr lo = some start) (hlt : x.addr lt = some left)
    (hgt : x.addr gt = some right) (hhi : x.addr hi = some stop)
    (h₁ : start.val ≤ left.val) (h₂ : right.val ≤ stop.val)
    (hzero : x.scalars zero = 0) (hone : x.scalars one = 1)
    (hslot : x.addr sp = some slot) (hroom : slot.val + 4 < n) :
    Program.ExecWithin (Local.instructionSet localModel n 16 16)
      (.seq countChildren pushLargerFirst) x (scheduledChildren x start left right stop slot hroom)
        (8 * (left.val - start.val) + 8 * (stop.val - right.val) + 27) := by
  let z := countedChildren x start left right stop
  have he := countChildren_exec x start left right stop hlo hlt hgt hhi h₁ h₂ hzero hone
  have hlo' : z.addr lo = some start := by simp [z, countedChildren, hlo]
  have hlt' : z.addr lt = some left := by simp [z, countedChildren, hlt]
  have hgt' : z.addr gt = some right := by simp [z, countedChildren, hgt]
  have hhi' : z.addr hi = some stop := by simp [z, countedChildren, hhi]
  have hzero' : z.scalars zero = 0 := by simp [z, countedChildren, hzero]
  have hone' : z.scalars one = 1 := by simp [z, countedChildren, hone]
  have hsp' : z.addr sp = some slot := by simp [z, countedChildren, hslot]
  have htest : (Local.instructionSet localModel n 16 16).Holds (.scalar () val tmp) z ↔
      left.val - start.val < stop.val - right.val := by simp [z, countedChildren]
  by_cases h : left.val - start.val < stop.val - right.val
  · have hp := localEnqueuePair_exec gt hi lo lt (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) z right stop start left slot
      hgt' hhi' hlo' hlt' h₂ h₁ hzero' hone' hsp' hroom
    simp only [scheduledChildren, ite_eq_left h]
    exact (Program.ExecWithin.seq he (Program.ExecWithin.branch_pos (htest.2 h) hp)).mono
      (by omega)
  · have hp := localEnqueuePair_exec lo lt gt hi (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) z start left right stop slot
      hlo' hlt' hgt' hhi' h₁ h₂ hzero' hone' hsp' hroom
    simp only [scheduledChildren, ite_eq_right h]
    exact (Program.ExecWithin.seq he (Program.ExecWithin.branch_neg (fun ht => h (htest.1 ht))
      hp)).mono (by omega)

/-- The result of one ranked phase, including the exact sizes and stack entries of both children. -/
@[expose] def PartitionResult {n w : ℕ} (x y : Local.Data localModel n 16 16)
    (start stop slot : Fin n) (rank : ℕ) (hrank : start.val + rank < stop.val)
    (hroom : slot.val + 4 < n) : Prop :=
  ∃ (z : Local.Data localModel n 16 16) (left right : Fin n),
    PartInv w start.val stop.val (x.values ⟨start.val + rank, hrank.trans stop.isLt⟩)
      (partitionView x).mem (partitionView z) ∧
    (partitionView z).regs cur = (partitionView z).regs gt ∧
    left.val = (partitionView z).regs lt ∧ right.val = (partitionView z).regs gt ∧
    left.val < right.val ∧
    z.addr sp = x.addr sp ∧ z.addr stackHi = x.addr stackHi ∧
    z.scalars zero = x.scalars zero ∧ z.refs = x.refs ∧
    (let input := memSlice start.val stop.val (partitionView x).mem
     let key := x.values ⟨start.val + rank, hrank.trans stop.isLt⟩
     left.val - start.val = input.countP (· < key) ∧
       stop.val - right.val = input.countP (key < ·)) ∧
    y = scheduledChildren z start left right stop slot hroom

/-- A full partition and scheduling phase for a supplied rank. The intermediate state satisfies
the numeric partition invariant, and the final state is obtained by recording the strict children
with the smaller child on top. Four prepared stack slots suffice for this phase. -/
theorem partitionAndEnqueue_exec {n w : ℕ} (x : Local.Data localModel n 16 16)
    (start stop slot : Fin n) (rank : ℕ)
    (hlo : x.addr lo = some start) (hhi : x.addr hi = some stop) (hslot : x.addr sp = some slot)
    (hoffset : x.scalars tmp = rank) (hzero : x.scalars zero = 0) (hone : x.scalars one = 1)
    (hrank : start.val + rank < stop.val) (hfit : Fits w stop.val) (hroom : slot.val + 4 < n) :
    ∃ y, Program.ExecWithin (Local.instructionSet localModel n 16 16)
        partitionAndEnqueue x y (19 * (stop.val - start.val) + 4 * rank + 35) ∧
      PartitionResult (w := w) x y start stop slot rank hrank hroom := by
  obtain ⟨z, hz, hinv, hmeet, hsp, hbase, hzero', hrefs⟩ :=
    partitionAtRank_exec x start stop rank hlo hhi hoffset hzero hone hrank hfit
  let left : Fin n := ⟨(partitionView z).regs lt,
    (hinv.lt_le_cur.trans (hinv.cur_le_gt.trans hinv.gt_le_hi)).trans_lt stop.isLt⟩
  let right : Fin n := ⟨(partitionView z).regs gt, hinv.gt_le_hi.trans_lt stop.isLt⟩
  have hleft := cursor_lookup z (r := lt) (by decide) left.isLt
  have hright := cursor_lookup z (r := gt) (by decide) right.isLt
  have hlo' := cursor_lookup z (r := lo) (by decide) (hinv.lo_eq ▸ start.isLt)
  have hhi' := cursor_lookup z (r := hi) (by decide) (hinv.hi_eq ▸ stop.isLt)
  have hzlo : z.addr lo = some start := hlo'.trans (congrArg some (Fin.ext hinv.lo_eq))
  have hzhi : z.addr hi = some stop := hhi'.trans (congrArg some (Fin.ext hinv.hi_eq))
  have hzone : z.scalars one = 1 := by
    simpa [partitionView, isAddressReg] using hinv.one_eq
  have hqueued := schedule_exec z start left right stop slot hzlo hleft hright hzhi
    hinv.lo_le_lt hinv.gt_le_hi (hzero'.trans hzero) hzone (hsp.trans hslot) hroom
  have hsize : left.val ≤ right.val := hinv.lt_le_cur.trans hinv.cur_le_gt
  have hkey : x.values ⟨start.val + rank, hrank.trans stop.isLt⟩ ∈
      memSlice start.val stop.val (partitionView x).mem := by
    refine mem_memSlice_iff.mpr ⟨start.val + rank, by omega, hrank, ?_⟩
    exact dite_eq_left (hrank.trans stop.isLt)
  obtain ⟨hstrict, hleftCount, hrightCount⟩ := partition_counts_and_lt
    ⟨hinv.lo_le_lt, hsize, hinv.gt_le_hi⟩ hinv.perm hinv.lt_zone
    (fun a ha hb => hinv.eq_zone a ha (hmeet.symm ▸ hb)) hinv.gt_zone hkey
  have hlower : start.val ≤ left.val := hinv.lo_le_lt
  have hupper : right.val ≤ stop.val := hinv.gt_le_hi
  refine ⟨scheduledChildren z start left right stop slot hroom, ?_, ?_⟩
  · exact (Program.ExecWithin.seq hz hqueued).mono (by omega)
  · exact ⟨z, left, right, hinv, hmeet, rfl, rfl, hstrict, hsp, hbase, hzero', hrefs,
      ⟨hleftCount, hrightCount⟩, rfl⟩

end Cslib.Algorithms.WordRAM.Quicksort
