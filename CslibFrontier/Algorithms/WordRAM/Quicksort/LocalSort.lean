/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.Quicksort.StackInvariant
public import CslibFrontier.Languages.Probabilistic.Expect

/-!
# Local-address quicksort loop

The program makes one unit-cost uniform rank draw per partition and walks to that rank by
following successors. It overwrites the input payload cells in place. The input records and
stack are prepared before execution.

The loop invariant pairs the live frames with the WordRAM sortedness and permutation invariants.
Each partition pushes the larger child first, so the smaller child is processed first. The prepared
stack needs two cells per frame and at most `Nat.log 2 n + 1` frames.
-/

public section

namespace Cslib.Algorithms.WordRAM.Quicksort

open Cslib.WordRAM Reg
open scoped ENNReal

private abbrev SortState (n : ℕ) := Local.Data localModel n 16 16
private abbrev sortSet (n : ℕ) := Local.instructionSet localModel n 16 16

/-- A frame at depth `i` from the bottom has length at most `n / 2^i`. -/
def DepthBound (n : ℕ) (S : List (ℕ × ℕ)) : Prop :=
  ∀ i (hi : i < S.length), (S[i].2 - S[i].1) * 2 ^ i ≤ n

private theorem depth_append {n : ℕ} {S : List (ℕ × ℕ)} {a b : ℕ}
    (hs : DepthBound n S) (hr : (b - a) * 2 ^ S.length ≤ n) :
    DepthBound n (S ++ [(a, b)]) := by
  intro i hi
  by_cases h : i < S.length
  · simpa only [List.getElem_append_left h] using hs i h
  · have he : i = S.length := by simp only [List.length_append, List.length_singleton] at hi; omega
    subst i
    simpa using hr

private theorem depth_queue {n : ℕ} {S : List (ℕ × ℕ)} {a b : ℕ}
    (hs : DepthBound n S) (hr : (b - a) * 2 ^ S.length ≤ n) :
    DepthBound n (queueRange S a b) := by
  by_cases h : a + 2 ≤ b
  · simpa only [queueRange, ite_eq_left h] using depth_append hs hr
  · simpa only [queueRange, ite_eq_right h] using hs

private theorem depth_length_le {n : ℕ} {S : List (ℕ × ℕ)}
    (hs : DepthBound n S) (hv : ValidStack n S) : S.length ≤ Nat.log 2 n + 1 := by
  rcases List.eq_nil_or_concat' S with rfl | ⟨T, ⟨a, b⟩, rfl⟩
  · simp
  · have hsize := (hv.1 (a, b) (by simp)).2.1
    have hdepth : (b - a) * 2 ^ T.length ≤ n := by
      simpa using hs T.length (by simp)
    have hpow := (Nat.le_mul_of_pos_left (2 ^ T.length) (show 0 < b - a by omega)).trans hdepth
    simpa only [List.length_append, List.length_singleton] using
      Nat.succ_le_succ (Nat.le_log_of_pow_le (by decide : 1 < 2) hpow)

/-- The number of interval cells prepared for an input of length `n`, including two cells per
stack frame and a fixed number of boundary cells. -/
@[expose] def preparedCapacity (n : ℕ) : ℕ :=
  n + 2 * (Nat.log 2 n + 1) + 6

private theorem input_lt_capacity (n : ℕ) : n + 4 < preparedCapacity n := by
  unfold preparedCapacity
  omega

/-- The prepared stack and the partial sorting invariant. -/
structure LocalSortInv {n : ℕ} (input : List ℕ) (x : Local.Data localModel n 16 16)
    (pending : List (ℕ × ℕ)) : Prop where
  stack : StackRealizes x (input.length + 2) pending
  valid : ValidStack input.length pending
  depth : DepthBound input.length pending
  base : ∃ b : Fin n, x.addr stackHi = some b ∧ b.val = input.length + 2
  zero : x.scalars zero = 0
  one : x.scalars one = 1
  perm : (memSlice 1 (input.length + 1) (partitionView x).mem).Perm input
  ordered : NoExternalInversions input.length (partitionView x).mem pending

private def replaceRange (S : List (ℕ × ℕ)) (a l r b : ℕ) : List (ℕ × ℕ) :=
  if l - a < b - r then queueRange (queueRange S r b) a l
  else queueRange (queueRange S a l) r b

private theorem queueRange_append (S : List (ℕ × ℕ)) (a b : ℕ) :
    queueRange S a b = S ++ queueRange [] a b := by
  by_cases h : a + 2 ≤ b <;> simp [queueRange, h]

private theorem replaceRange_perm (S : List (ℕ × ℕ)) (a l r b : ℕ) :
    (replaceRange S a l r b).Perm (queueRange (queueRange S a l) r b) := by
  by_cases h : l - a < b - r
  · rw [replaceRange, ite_eq_left h, queueRange_append (queueRange S r b) a l,
      queueRange_append (queueRange S a l) r b, queueRange_append S r b,
      queueRange_append S a l, List.append_assoc, List.append_assoc]
    exact List.perm_append_comm.append_left S
  · simp [replaceRange, h]

private theorem depth_smaller_last {n parent : ℕ} {S : List (ℕ × ℕ)} {a b c d : ℕ}
    (hs : DepthBound n S) (hp : parent * 2 ^ S.length ≤ n)
    (hbig : b - a ≤ parent) (hsmall : 2 * (d - c) ≤ parent) :
    DepthBound n (queueRange (queueRange S a b) c d) := by
  apply depth_queue (depth_queue hs ((Nat.mul_le_mul_right _ hbig).trans hp))
  have hl : d - c ≤ parent := by omega
  have hm := (Nat.mul_le_mul_right (2 ^ S.length) hsmall).trans hp
  by_cases h : a + 2 ≤ b
  · simpa [queueRange, h, pow_succ, Nat.mul_left_comm, Nat.mul_comm, Nat.mul_assoc] using hm
  · simpa only [queueRange, ite_eq_right h] using (Nat.mul_le_mul_right _ hl).trans hp

private theorem depth_replace {n : ℕ} {S : List (ℕ × ℕ)} {a l r b : ℕ}
    (hs : DepthBound n (S ++ [(a, b)])) (hal : a ≤ l) (hlr : l < r) (hrb : r ≤ b) :
    DepthBound n (replaceRange S a l r b) := by
  have hp : (b - a) * 2 ^ S.length ≤ n := by simpa using hs S.length (by simp)
  have hprefix : DepthBound n S := by
    intro i hi
    have hb : i < (S ++ [(a, b)]).length := by simp only [List.length_append]; omega
    have hentry := hs i hb
    change (((S ++ [(a, b)])[i]'hb).2 - ((S ++ [(a, b)])[i]'hb).1) * 2 ^ i ≤ n at hentry
    rw [List.getElem_append_left hi] at hentry
    exact hentry
  by_cases h : l - a < b - r
  · rw [replaceRange, ite_eq_left h]
    exact depth_smaller_last hprefix hp (by omega) (by omega)
  · rw [replaceRange, ite_eq_right h]
    exact depth_smaller_last hprefix hp (by omega) (by omega)

private theorem phase_preserves {n w : ℕ} {input : List ℕ} {S : List (ℕ × ℕ)}
    {x y : SortState n} (start stop slot : Fin n) (rank : ℕ)
    (hrank : start.val + rank < stop.val) (hroom : slot.val + 4 < n)
    (hs : LocalSortInv input x (S ++ [(start.val, stop.val)]))
    (hslot : slot.val = input.length + 2 + 2 * S.length)
    (hphase : PartitionResult (w := w) (rankedFrame x start stop slot rank) y
      start stop slot rank hrank hroom) :
    ∃ l r, start.val ≤ l ∧ l < r ∧ r ≤ stop.val ∧
      LocalSortInv input y (replaceRange S start.val l r stop.val) ∧
      let data := memSlice start.val stop.val (partitionView x).mem
      let pivot := x.values ⟨start.val + rank, hrank.trans stop.isLt⟩
      l - start.val = data.countP (· < pivot) ∧ stop.val - r = data.countP (pivot < ·) := by
  obtain ⟨z, left, right, hinv, hmeet, hleft, hright, hstrict, hsp, hbase, hzero, hrefs,
    hcounts, rfl⟩ := hphase
  let base := input.length + 2
  let measured := countedChildren z start left right stop
  let out := scheduledChildren z start left right stop slot hroom
  have hspz : z.addr sp = some slot := by simpa [rankedFrame] using hsp
  have hspm : measured.addr sp = some slot := by simp [measured, countedChildren, hspz]
  have hinput : input.length + 2 < n := by
    obtain ⟨b, _, hb⟩ := hs.base
    exact hb ▸ b.isLt
  have hxmem : (partitionView (rankedFrame x start stop slot rank)).mem =
      (partitionView x).mem := partitionView_mem_congr rfl
  have hstart : 1 ≤ start.val :=
    (hs.valid.1 _ (List.mem_append_right _ (List.mem_singleton_self _))).1
  have hstop : stop.val ≤ input.length + 1 :=
    (hs.valid.1 _ (List.mem_append_right _ (List.mem_singleton_self _))).2.2
  have hleft' : start.val ≤ left.val := hleft.symm ▸ hinv.lo_le_lt
  have hright' : right.val ≤ stop.val := hright.symm ▸ hinv.gt_le_hi
  have hsz : StackRealizes z base S := by
    have hpop := hs.stack.pop (y := rankedFrame x start stop slot rank) slot hslot
      (by simp [rankedFrame]) rfl rfl
    refine hpop.frames_congr hsp ?_ (fun a _ _ => congrFun hrefs a)
    intro a ha _
    rw [← partitionView_mem z a, ← partitionView_mem (rankedFrame x start stop slot rank) a]
    exact (hinv.modifies a.val (by
      simp only [Finset.mem_Ico]
      change input.length + 2 ≤ a.val at ha
      omega))
  have hsm : StackRealizes measured base S :=
    hsz.frames_congr (hspm.trans hspz.symm) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
  have hout : StackRealizes out base (replaceRange S start.val left.val right.val stop.val) ∧
      (∀ j : Fin n, j.val < slot.val → out.values j = measured.values j) ∧
      out.addr stackHi = measured.addr stackHi ∧ out.scalars zero = measured.scalars zero ∧
      out.scalars one = measured.scalars one := by
    by_cases h : left.val - start.val < stop.val - right.val
    · simpa only [out, scheduledChildren, replaceRange, ite_eq_left h, measured] using
        hsm.enqueuePair right stop start left slot hroom hspm
    · simpa only [out, scheduledChildren, replaceRange, ite_eq_right h, measured] using
        hsm.enqueuePair start left right stop slot hroom hspm
  have horder := replaceRange_perm S start.val left.val right.val stop.val
  have hvalid := (validStack_push_children hs.valid ⟨hleft', hstrict, hright'⟩).2
  have hvalid' : ValidStack input.length (replaceRange S start.val left.val right.val stop.val) :=
    ⟨fun p hp => hvalid.1 p (horder.mem_iff.mp hp),
      (horder.pairwise_iff IntervalDisjoint.symm).mpr hvalid.2⟩
  have hcongr : ∀ i, 1 ≤ i → i < input.length + 1 →
      (partitionView out).mem i = (partitionView z).mem i := by
    intro i _ hi
    let a : Fin n := ⟨i, by omega⟩
    have ha : a.val < slot.val := by dsimp [a]; omega
    change (partitionView out).mem a.val = (partitionView z).mem a.val
    rw [partitionView_mem, partitionView_mem]
    exact (hout.2.1 a ha).trans (by simp [measured, countedChildren])
  have hp := perm_full_of_subslice (n := input.length) ⟨hstart, by omega, hstop⟩
    hinv.perm hinv.modifies
  have hp' : (memSlice 1 (input.length + 1) (partitionView out).mem).Perm input := by
    rw [memSlice_congr hcongr]
    exact ((by simpa only [hxmem] using hp :
      (memSlice 1 (input.length + 1) (partitionView z).mem).Perm
        (memSlice 1 (input.length + 1) (partitionView x).mem))).trans hs.perm
  have heq : ∀ i, left.val ≤ i → i < right.val →
      (partitionView z).mem i = x.values ⟨start.val + rank, hrank.trans stop.isLt⟩ := by
    intro i hi hj
    exact hinv.eq_zone i (hleft ▸ hi) (hmeet.symm ▸ (hright ▸ hj))
  have hno : NoExternalInversions input.length (partitionView z).mem
      (queueRange (queueRange S start.val left.val) right.val stop.val) := by
    apply noExternalInversions_after_partition hs.valid hs.ordered
      ⟨hleft', hstrict, hright'⟩
    · simpa only [hxmem] using hinv.perm
    · simpa only [hxmem] using hinv.modifies
    · simpa only [hleft] using hinv.lt_zone
    · exact heq
    · simpa only [hright] using hinv.gt_zone
  obtain ⟨b, hb, hbval⟩ := hs.base
  have hbasez : z.addr stackHi = some b := by simpa [rankedFrame, hb] using hbase
  have honez : z.scalars one = 1 := (partitionView_one z).symm.trans hinv.one_eq
  have hzeroz : z.scalars zero = 0 := by simpa [rankedFrame, hs.zero] using hzero
  refine ⟨left.val, right.val, hleft', hstrict, hright',
    ⟨hout.1, hvalid', depth_replace hs.depth hleft' hstrict hright', ?_, ?_, ?_, hp', ?_⟩, ?_⟩
  · exact ⟨b, hout.2.2.1.trans (by simp [measured, countedChildren, hbasez]), hbval⟩
  · exact hout.2.2.2.1.trans (by simp [measured, countedChildren, hzeroz])
  · exact hout.2.2.2.2.trans (by simp [measured, countedChildren, honez])
  · intro i j hi hij hj hnot
    rw [hcongr i hi (hij.trans hj), hcongr j (hi.trans hij.le) hj]
    exact hno i j hi hij hj fun p hp => hnot p (horder.mem_iff.mpr hp)
  · rw [hxmem] at hcounts
    exact hcounts

private noncomputable def pendingRanges {n : ℕ} (input : List ℕ) (x : SortState n) :
    List (ℕ × ℕ) := by
  classical
  exact if h : ∃ S, StackRealizes x (input.length + 2) S then h.choose else []

private theorem pending_eq {n : ℕ} {input : List ℕ} {x : SortState n} {S : List (ℕ × ℕ)}
    (h : StackRealizes x (input.length + 2) S) : pendingRanges input x = S := by
  classical
  unfold pendingRanges
  rw [dite_eq_left (show ∃ T, StackRealizes x (input.length + 2) T from ⟨S, h⟩)]
  exact StackRealizes.unique (Classical.choose_spec (show ∃ T, StackRealizes x (input.length + 2) T
    from ⟨S, h⟩)) h

private def stackMass (S : List (ℕ × ℕ)) : ℕ := (S.map fun r => r.2 - r.1).sum

private noncomputable def stackPotential (S : List (ℕ × ℕ)) : ℝ :=
  (S.map fun r => 2 * subCost (r.2 - r.1)).sum

private theorem stackPotential_nonneg (S : List (ℕ × ℕ)) : 0 ≤ stackPotential S := by
  apply List.sum_nonneg
  intro x hx
  obtain ⟨r, _, rfl⟩ := List.mem_map.mp hx
  exact mul_nonneg (by norm_num) (subCost_nonneg _)

private theorem stackMass_children {S : List (ℕ × ℕ)} {a l r b : ℕ}
    (hal : a ≤ l) (hlr : l < r) (hrb : r ≤ b) :
    stackMass (replaceRange S a l r b) < stackMass (S ++ [(a, b)]) := by
  unfold stackMass
  rw [((replaceRange_perm S a l r b).map _).sum_eq]
  unfold queueRange
  split_ifs <;> simp <;> omega

private theorem stackPotential_children {S : List (ℕ × ℕ)} {a l r b : ℕ}
    (hal : a ≤ l) (hrb : r ≤ b) :
    stackPotential (replaceRange S a l r b) =
      stackPotential S + 2 * (subCost (l - a) + subCost (b - r)) := by
  unfold stackPotential
  rw [((replaceRange_perm S a l r b).map _).sum_eq]
  by_cases h₁ : a + 2 ≤ l
  · by_cases h₂ : r + 2 ≤ b
    · simp [queueRange, h₁, h₂]
      ring
    · simp [queueRange, h₁, h₂, subCost_of_lt_two (m := b - r) (by omega)]
  · by_cases h₂ : r + 2 ≤ b
    · simp [queueRange, h₁, h₂, subCost_of_lt_two (m := l - a) (by omega)]
    · simp [queueRange, h₁, h₂, subCost_of_lt_two (m := l - a) (by omega),
        subCost_of_lt_two (m := b - r) (by omega)]

private theorem stack_empty_iff {n : ℕ} {input : List ℕ} {x : SortState n} {S : List (ℕ × ℕ)}
    (h : LocalSortInv input x S) : x.addr sp = x.addr stackHi ↔ S = [] := by
  obtain ⟨b, hb, hbase⟩ := h.base
  obtain ⟨p, hp, htop⟩ := h.stack.top
  rw [hp, hb]
  constructor
  · intro he
    have he' := congrArg Fin.val (Option.some.inj he)
    exact List.length_eq_zero_iff.mp (by omega)
  · rintro rfl
    exact congrArg some (Fin.ext (by simpa using htop.trans (by simpa using hbase.symm)))

private abbrev invariant {n : ℕ} (input : List ℕ) (x : SortState n) : Prop :=
  LocalSortInv input x (pendingRanges input x)

private noncomputable def mass {n : ℕ} (input : List ℕ) (x : SortState n) : ℕ :=
  stackMass (pendingRanges input x)

private noncomputable def potential {n : ℕ} (input : List ℕ) (x : SortState n) : ℝ≥0∞ :=
  ENNReal.ofReal (stackPotential (pendingRanges input x))

private theorem phase_average (u : List ℕ) {m : ℕ} (hlen : u.length = m) (hm : 2 ≤ m)
    (t : Fin (m - 1 + 1) → ℕ) (ht : ∀ k, t k ≤ 19 * m + 4 * k.val + 35)
    (base : ℝ) (hb : 0 ≤ base) :
    ProbComp.expect (ProbComp.unifFin (m - 1)) (fun k =>
      (↑(6 + t k) : ℝ≥0∞) + 2 + ENNReal.ofReal (base +
        2 * (subCost (u.countP (· < u[k.val]'(by have := k.isLt; omega))) +
          subCost (u.countP (u[k.val]'(by have := k.isLt; omega) < ·))))) ≤
      ENNReal.ofReal (base + 2 * subCost m) := by
  let e : Fin (m - 1 + 1) ≃ Fin u.length := finCongr (by omega)
  let f (k : Fin u.length) : ℝ := ((8 + t (e.symm k) : ℕ) : ℝ) +
    2 * (subCost (u.countP (· < u[k.val])) + subCost (u.countP (u[k.val] < ·)))
  have havg : (∑ k : Fin u.length, f k) / (u.length : ℝ) ≤ 2 * subCost m := by
    simpa only [hlen] using localIteration_average_le u (by omega) (fun k => t (e.symm k))
      (fun k => by simpa [e, hlen] using ht (e.symm k))
  have hpos : (0 : ℝ) < u.length := by exact_mod_cast (by omega : 0 < u.length)
  have hden : ((m - 1 : ℕ) : ℝ≥0∞) + 1 = ENNReal.ofReal (u.length : ℝ) := by
    rw [ENNReal.ofReal_natCast]
    exact_mod_cast (by omega : m - 1 + 1 = u.length)
  rw [ProbComp.expect_unifFin, hden]
  have heq : ∀ k : Fin (m - 1 + 1),
      (↑(6 + t k) : ℝ≥0∞) + 2 + ENNReal.ofReal (base +
        2 * (subCost (u.countP (· < u[k.val]'(by have := k.isLt; omega))) +
          subCost (u.countP (u[k.val]'(by have := k.isLt; omega) < ·)))) =
        ENNReal.ofReal (base + f (e k)) := by
    intro k
    simp only [f, Equiv.symm_apply_apply]
    have hv : (e k).val = k.val := rfl
    simp only [hv]
    have hcast : (↑(6 + t k) : ℝ≥0∞) + 2 = ENNReal.ofReal ((8 + t k : ℕ) : ℝ) := by
      rw [ENNReal.ofReal_natCast]
      push_cast
      norm_num [add_assoc, add_left_comm, add_comm]
    have hchild : 0 ≤ base + 2 * (subCost (u.countP (· < u[k.val]'(by have := k.isLt; omega))) +
        subCost (u.countP (u[k.val]'(by have := k.isLt; omega) < ·))) :=
      add_nonneg hb (mul_nonneg (by norm_num) (add_nonneg (subCost_nonneg _) (subCost_nonneg _)))
    rw [hcast, ← ENNReal.ofReal_add (by positivity) hchild]
    congr 1
    ring
  simp only [heq]
  have hsum := Fintype.sum_equiv e (fun k => ENNReal.ofReal (base + f (e k)))
    (fun k => ENNReal.ofReal (base + f k)) (fun _ => rfl)
  rw [hsum, ← ENNReal.ofReal_sum_of_nonneg
      (fun k _ => add_nonneg hb (by
        dsimp [f]
        exact add_nonneg (by positivity) (mul_nonneg (by norm_num)
          (add_nonneg (subCost_nonneg _) (subCost_nonneg _))))),
    ← ENNReal.ofReal_div_of_pos hpos]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    add_div, mul_div_cancel_left₀ _ hpos.ne']
  exact add_le_add le_rfl havg

private def stackEmpty : Local.Test localModel 16 16 := .addrEq sp stackHi

/-- Repeat the verified randomized iteration until the prepared stack is empty. -/
def localSortLoop : Program.Code (Local.Op localModel 16 16) (Local.Test localModel 16 16) :=
  .loopUntil stackEmpty localIteration

private theorem iteration_step {n w : ℕ} {input : List ℕ}
    (hcap : preparedCapacity input.length ≤ n) (hfit : Fits w (input.length + 1))
    (x : SortState n) (hx : invariant input x) (hactive : ¬(sortSet n).Holds stackEmpty x) :
    ∃ m, Program.ExecRand (I := sortSet n) (Local.evalRand localKernel) localIteration x m ∧
      (∀ z ∈ m.support, invariant input z.1 ∧ mass input z.1 < mass input x ∧
        z.2 + 2 ≤ 23 * input.length + 39) ∧
      ProbComp.expect m (fun z => (z.2 : ℝ≥0∞) + 2 + potential input z.1) ≤
        potential input x := by
  let pending := pendingRanges input x
  change LocalSortInv input x pending at hx
  have hne : pending ≠ [] := fun he => hactive ((stack_empty_iff hx).2 he)
  obtain ⟨S, ⟨a, b⟩, hS⟩ := (List.eq_nil_or_concat' pending).resolve_left hne
  have hxS : LocalSortInv input x (S ++ [(a, b)]) := hS ▸ hx
  obtain ⟨slot, start, stop, hslotEnd, hslot, ha, hb, hsp, hfirst, hlast, hlen⟩ :=
    hxS.stack.last
  have hvalid := hxS.valid.1 (a,b) (by simp)
  have hroom : slot.val + 4 < n := by
    have hlenBound := depth_length_le hxS.depth hxS.valid
    unfold preparedCapacity at hcap
    simp only [List.length_append, List.length_singleton] at hlenBound
    omega
  have hnontrivial : start.val + 2 ≤ stop.val := by omega
  have hstopfit : Fits w stop.val := hfit.of_le (by omega)
  let len := stop.val - start.val
  have hlen₂ : 2 ≤ len := by dsimp [len]; omega
  have hlenInput : len ≤ input.length := by dsimp [len]; omega
  obtain ⟨y, t, hrun, hpost⟩ := localIteration_exec x start stop slot hroom hsp hfirst hlast
    hlen hnontrivial hxS.zero hxS.one hstopfit
  have hx' : LocalSortInv input x (S ++ [(start.val, stop.val)]) := by
    simpa only [ha, hb] using hxS
  have hphase (k : Fin (len - 1 + 1)) :=
    phase_preserves start stop slot k.val (by
      have hk := k.isLt
      change k.val < stop.val - start.val - 1 + 1 at hk
      omega) hroom hx' hslot (hpost k).2
  have hxpending : pendingRanges input x = S ++ [(start.val, stop.val)] := pending_eq hx'.stack
  refine ⟨_, hrun, ?_, ?_⟩
  · intro z hz
    obtain ⟨k, _, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz
    obtain ⟨l, r, hal, hlr, hrb, hInv, _⟩ := hphase k
    have hp := pending_eq hInv.stack
    refine ⟨by simpa only [invariant, hp] using hInv, ?_, ?_⟩
    · simpa only [mass, hp, hxpending] using stackMass_children (S := S) hal hlr hrb
    · have hk := k.isLt
      have hc := (hpost k).1
      change t k ≤ 19 * len + 4 * k.val + 35 at hc
      change 6 + t k + 2 ≤ 23 * input.length + 39
      omega
  · let u := memSlice start.val stop.val (partitionView x).mem
    have hu : u.length = len := length_memSlice _ _ _
    rw [ProbComp.expect_map]
    have hB := phase_average u hu hlen₂ t (fun k => (hpost k).1)
      (stackPotential S) (stackPotential_nonneg S)
    have hB' := hB
    rw [potential, hxpending]
    change _ ≤ ENNReal.ofReal (stackPotential (S ++ [(start.val, stop.val)]))
    have heq : stackPotential (S ++ [(start.val, stop.val)]) =
        stackPotential S + 2 * subCost len := by
      simp [stackPotential, len]
    rw [heq]
    refine (ProbComp.expect_mono ?_).trans hB'
    intro k
    obtain ⟨l, r, hal, hlr, hrb, hInv, hleft, hright⟩ := hphase k
    have hp := pending_eq hInv.stack
    have hk : k.val < len := by have := k.isLt; omega
    have hget : u[k.val]'(by omega) =
        x.values ⟨start.val + k.val, by have := stop.isLt; dsimp [len] at hk; omega⟩ := by
      rw [getElem_memSlice (show k.val < stop.val - start.val from hk)]
      exact partitionView_mem x ⟨start.val + k.val, by have := stop.isLt; dsimp [len] at hk; omega⟩
    change (↑(6 + t k) : ℝ≥0∞) + 2 + potential input (y k) ≤ _
    rw [potential, hp, stackPotential_children hal hrb, hleft, hright, ← hget]

private theorem loop_with_bound {n : ℕ} (input : List ℕ) (K : ℕ)
    (step : ∀ x : SortState n, invariant input x → ¬(sortSet n).Holds stackEmpty x →
      ∃ m, Program.ExecRand (I := sortSet n) (Local.evalRand localKernel) localIteration x m ∧
        (∀ z ∈ m.support, invariant input z.1 ∧ mass input z.1 < mass input x ∧ z.2 + 2 ≤ K) ∧
        ProbComp.expect m (fun z => (z.2 : ℝ≥0∞) + 2 + potential input z.1) ≤ potential input x)
    (x : SortState n) (hx : invariant input x) :
    ∃ m, Program.ExecRand (I := sortSet n) (Local.evalRand localKernel) localSortLoop x m ∧
      (∀ z ∈ m.support, invariant input z.1 ∧ (sortSet n).Holds stackEmpty z.1 ∧
        z.2 ≤ K * mass input x + 1) ∧
      ProbComp.expect m (fun z => (z.2 : ℝ≥0∞)) ≤ potential input x + 1 := by
  classical
  induction hm : mass input x using Nat.strong_induction_on generalizing x with
  | _ measure ih =>
    by_cases ht : (sortSet n).Holds stackEmpty x
    · refine ⟨pure (x, 1), Program.ExecRand.loopUntil_exit ht, ?_, ?_⟩
      · intro z hz
        obtain rfl := OracleComp.eq_of_mem_supportWith_pure hz
        exact ⟨hx, ht, Nat.le_add_left _ _⟩
      · rw [ProbComp.expect_pure]
        simp only [Nat.cast_one]
        exact le_add_self
    · obtain ⟨m, he, hsupport, hdrift⟩ := step x hx ht
      let Good (s : SortState n) (q : ProbComp (SortState n × ℕ)) :=
        Program.ExecRand (I := sortSet n) (Local.evalRand localKernel) localSortLoop s q ∧
          (∀ z ∈ q.support, invariant input z.1 ∧ (sortSet n).Holds stackEmpty z.1 ∧
            z.2 ≤ K * mass input s + 1) ∧
          ProbComp.expect q (fun z => (z.2 : ℝ≥0∞)) ≤ potential input s + 1
      let next (s : SortState n) : ProbComp (SortState n × ℕ) :=
        if h : ∃ q, Good s q then h.choose else pure (s, 0)
      have hnext (z : SortState n × ℕ) (hz : z ∈ m.support) : Good z.1 (next z.1) := by
        have hs := hsupport z hz
        have hex : ∃ q, Good z.1 q := ih _ (hm ▸ hs.2.1) z.1 hs.1 rfl
        have hn : next z.1 = Classical.choose hex := by
          exact dite_eq_left hex
        rw [hn]
        exact Classical.choose_spec hex
      refine ⟨_, Program.ExecRand.loopUntil_iter ht he fun z hz => (hnext z hz).1, ?_, ?_⟩
      · intro y hy
        obtain ⟨z, hz, h⟩ := OracleComp.mem_supportWith_bind_iff.mp hy
        obtain ⟨u, hu, hu'⟩ := OracleComp.mem_supportWith_bind_iff.mp h
        obtain rfl := OracleComp.eq_of_mem_supportWith_pure hu'
        obtain ⟨hi, hstop, htime⟩ := (hnext z hz).2.1 u hu
        refine ⟨hi, hstop, ?_⟩
        have hrank := (hsupport z hz).2.1
        have hbody := (hsupport z hz).2.2
        have hmul := Nat.mul_le_mul_left K (show mass input z.1 + 1 ≤ mass input x by omega)
        rw [Nat.mul_add, Nat.mul_one, hm] at hmul
        change z.2 + u.2 + 2 ≤ K * measure + 1
        omega
      · rw [ProbComp.expect_bind]
        calc
          _ ≤ ProbComp.expect m (fun z =>
              ((z.2 : ℝ≥0∞) + 2 + potential input z.1) + 1) := by
            refine ProbComp.expect_mono_on_support fun z hz => ?_
            rw [ProbComp.expect_bind]
            simp only [ProbComp.expect_pure, Nat.cast_add, Nat.cast_ofNat]
            have hcost : (fun u : SortState n × ℕ => (z.2 : ℝ≥0∞) + u.2 + 2) =
                (fun u => ((z.2 : ℝ≥0∞) + 2) + u.2) := by funext u; ac_rfl
            rw [hcost, ProbComp.expect_add, ProbComp.expect_const]
            exact (add_le_add le_rfl (hnext z hz).2.2).trans_eq (by ac_rfl)
          _ ≤ _ := by
            rw [ProbComp.expect_add, ProbComp.expect_const]
            exact add_le_add hdrift le_rfl

private def rootRanges (input : List ℕ) : List (ℕ × ℕ) :=
  if 2 ≤ input.length then [(1, input.length + 1)] else []

/-- Prepared local quicksort state. The first input cell is at address one. The stack base is
one cell beyond the exclusive input endpoint. A nontrivial input starts with a single frame. -/
def localSortInput (input : List ℕ) : Local.Data localModel (preparedCapacity input.length) 16 16 :=
  let n := input.length
  have hcap := input_lt_capacity input.length
  let b : Fin (preparedCapacity input.length) := ⟨n + 2, by omega⟩
  let p : Fin (preparedCapacity input.length) := ⟨n + 2 + 2 * (rootRanges input).length, by
    simp only [rootRanges]
    split <;> simp <;> omega⟩
  { addr := fun r => if r = stackHi then some b else if r = sp then some p else none
    scalars := fun r => if r = one then 1 else 0
    values := fun a => if a.val = n + 2 then n else input[a.val - 1]?.getD 0
    refs := fun a =>
      if a.val = n + 2 then some ⟨1, by omega⟩
      else if a.val = n + 3 then some ⟨n + 1, by omega⟩ else none }

private theorem localSortInput_realizes (input : List ℕ) :
    memSlice 1 (input.length + 1) (partitionView (localSortInput input)).mem = input := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    have hcap := input_lt_capacity input.length
    let a : Fin (preparedCapacity input.length) := ⟨1 + i, by omega⟩
    rw [getElem_memSlice (by omega : i < input.length + 1 - 1)]
    change (partitionView (localSortInput input)).mem a.val = _
    rw [partitionView_mem]
    have ha : a.val ≠ input.length + 2 := by dsimp [a]; omega
    have hindex : a.val - 1 = i := by dsimp [a]; omega
    simp [localSortInput, ha, hindex, List.getElem?_eq_getElem hj]

private theorem localSortInput_inv (input : List ℕ) :
    LocalSortInv input (localSortInput input) (rootRanges input) := by
  let x := localSortInput input
  have hcap := input_lt_capacity input.length
  let b : Fin (preparedCapacity input.length) := ⟨input.length + 2, by omega⟩
  have hp : ∃ p : Fin (preparedCapacity input.length), x.addr sp = some p ∧
      p.val = input.length + 2 + 2 * (rootRanges input).length := by
    exact ⟨⟨_, by
      unfold rootRanges
      split <;> simp <;> omega⟩, by simp [x, localSortInput], rfl⟩
  refine ⟨⟨hp, ?_⟩, ?_, ?_, ⟨b, by simp [b, localSortInput], rfl⟩,
    by simp [localSortInput], by simp [localSortInput],
    ?_, ?_⟩
  · by_cases h : 2 ≤ input.length
    · intro i
      have hi : i.val = 0 := by
        have hh := i.isLt
        simp [rootRanges, h] at hh
        omega
      have hidx : (rootRanges input)[i.val] = (1, input.length + 1) := by
        simp [rootRanges, h, hi]
      refine ⟨b, ⟨1, by omega⟩, ⟨input.length + 1, by omega⟩, by dsimp [b]; omega,
        ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [b, hi]
      · simp [hidx]
      · simp [hidx]
      · simp [b, localSortInput]
      · simp [b, localSortInput, Nat.add_assoc]
      · simp [b, localSortInput]
    · intro i
      have hh := i.isLt
      simp [rootRanges, h] at hh
  · by_cases h : 2 ≤ input.length
    · simp [rootRanges, h, ValidStack]
    · simp [rootRanges, h, ValidStack]
  · intro i hi
    by_cases h : 2 ≤ input.length
    · have hzero : i = 0 := by simpa [rootRanges, h] using hi
      subst i
      simp [rootRanges, h]
    · simp [rootRanges, h] at hi
  · rw [localSortInput_realizes]
  · intro i j hi hij hj hno
    by_cases h : 2 ≤ input.length
    · exact (hno (1, input.length + 1) (by simp [rootRanges, h]) ⟨hi, hj⟩).elim
    · omega

private theorem sorted_of_empty {n : ℕ} {input : List ℕ} {x : SortState n}
    (h : LocalSortInv input x []) :
    memSlice 1 (input.length + 1) (partitionView x).mem = input.mergeSort := by
  have hs : (memSlice 1 (input.length + 1) (partitionView x).mem).Pairwise (· ≤ ·) := by
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj hij
    simp only [length_memSlice] at hi hj
    rw [getElem_memSlice hi, getElem_memSlice hj]
    exact h.ordered (1 + i) (1 + j) (by omega) (by omega) (by omega)
      (fun p hp => (List.not_mem_nil hp).elim)
  exact (h.perm.trans (List.mergeSort_perm input _).symm).eq_of_pairwise' hs
    (List.pairwise_mergeSort' (· ≤ ·) input)

private theorem rootPotential_bound (input : List ℕ) :
    stackPotential (rootRanges input) ≤
      256 * (input.length : ℝ) * (Nat.log 2 input.length + 1) := by
  by_cases hm : 2 ≤ input.length
  · have hlen : (1 : ℝ) ≤ input.length := by exact_mod_cast (by omega : 1 ≤ input.length)
    have hlog : ((harmonic input.length : ℚ) : ℝ) ≤ Nat.log 2 input.length + 1 := by
      exact_mod_cast harmonic_le_log_add_one input.length
    simp only [rootRanges, ite_eq_left hm, stackPotential, List.map_singleton,
      List.sum_singleton, Nat.add_sub_cancel_right]
    calc
      2 * subCost input.length ≤ 128 * ((input.length : ℝ) + 1) * (harmonic input.length : ℝ) := by
        linarith [subCost_le_formula input.length]
      _ ≤ 128 * ((input.length : ℝ) + 1) * (Nat.log 2 input.length + 1) := by gcongr
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        linarith
  · simp only [rootRanges, ite_eq_right hm, stackPotential, List.map_nil, List.sum_nil]
    positivity

/-- From its prepared input, local quicksort sorts on every path and has a quadratic pathwise
instruction budget and an `O(n log n)` expected instruction bound. -/
theorem localSort_exec (input : List ℕ) :
    let n := input.length
    ∃ m : ProbComp (Local.Data localModel (preparedCapacity n) 16 16 × ℕ),
      Program.ExecRand (I := Local.instructionSet localModel (preparedCapacity n) 16 16)
        (Local.evalRand localKernel) localSortLoop (localSortInput input) m ∧
      (∀ z ∈ m.support, z.2 ≤ (23 * n + 39) * n + 1 ∧
        memSlice 1 (n + 1) (partitionView z.1).mem = input.mergeSort) ∧
      ProbComp.expect m (fun z => (z.2 : ℝ≥0∞)) ≤
        ENNReal.ofReal (256 * (n : ℝ) * (Nat.log 2 n + 1)) + 1 := by
  intro n
  let x := localSortInput input
  have hinit := localSortInput_inv input
  have hpending : pendingRanges input x = rootRanges input := pending_eq hinit.stack
  have hx : invariant input x := by simpa only [invariant, hpending] using hinit
  have hfit : Fits (logWidth 3 n) (n + 1) :=
    (fits_three_mul_add_three (w := logWidth 3 n) (n := n) le_rfl).of_le (by omega)
  obtain ⟨m, hrun, hs, he⟩ := loop_with_bound input (23 * n + 39)
    (fun s hs ht => iteration_step (by rfl) hfit s hs ht) x hx
  have hmass : mass input x ≤ n := by
    rw [mass, hpending]
    exact hinit.valid.sum_len_le
  refine ⟨m, hrun, ?_, ?_⟩
  · intro z hz
    obtain ⟨hi, hempty, htime⟩ := hs z hz
    have hstack : pendingRanges input z.1 = [] := (stack_empty_iff hi).1 hempty
    exact ⟨htime.trans (by gcongr), sorted_of_empty (hstack ▸ hi)⟩
  · refine he.trans (add_le_add ?_ le_rfl)
    rw [potential, hpending]
    exact ENNReal.ofReal_le_ofReal (rootPotential_bound input)

/-- Read the `n` input payloads in interval order from the compiled machine's heap. -/
def pointerSortOutput (n : ℕ) (x : Cslib.PointerMachine.State localModel (Local.layout 16 16)) :
    List ℕ :=
  memSlice 1 (n + 1) fun i => (x.heap[i]?).elim 0 fun r => r.data 0

private theorem pointerSortOutput_encode {n : ℕ} (x : SortState (preparedCapacity n)) :
    pointerSortOutput n (Local.encode x) = memSlice 1 (n + 1) (partitionView x).mem := by
  apply memSlice_congr
  intro i _ hi
  have hc := input_lt_capacity n
  let a : Fin (preparedCapacity n) := ⟨i, by omega⟩
  have hh : a.val < (Local.encode x).heap.length := by simp
  rw [List.getElem?_eq_getElem hh]
  exact (Local.encode_heap_getElem_data x a hh).trans (partitionView_mem x a).symm

/-- The compiled randomized pointer-machine quicksort sorts the payloads on the prepared
linked interval. Its structured execution witnesses the expected instruction bound, and the
assembled program reaches the halt within the stated pathwise budget. -/
theorem pointerSort_exec (input : List ℕ) :
    let n := input.length
    let x := Local.encode (localSortInput input)
    let c := Local.compile localSortLoop
    let R := Local.randomizedFlatMachine (M := localModel) (p := 16) (d := 16) localKernel
    ∃ m : ProbComp (Local.Data localModel (preparedCapacity n) 16 16 × ℕ),
      Program.ExecRand (I := Cslib.PointerMachine.instructionSet localModel (Local.layout 16 16))
        (Local.evalPointerRand localKernel) c x ((fun z => (Local.encode z.1, z.2)) <$> m) ∧
      R.run c.program ((23 * n + 39) * n + 1) (R.running 0 x) =
        ((fun z => R.running c.size (Local.encode z.1)) <$> m) ∧
      (∀ cfg ∈ (R.run c.program ((23 * n + 39) * n + 1) (R.running 0 x)).support,
        ∃ y, cfg = R.running c.size y ∧ pointerSortOutput n y = input.mergeSort ∧
          y.heap.length = preparedCapacity n) ∧
      ProbComp.expect ((fun z => (Local.encode z.1, z.2)) <$> m) (fun z => (z.2 : ℝ≥0∞)) ≤
        ENNReal.ofReal (256 * (n : ℝ) * (Nat.log 2 n + 1)) + 1 := by
  intro n x c R
  obtain ⟨m, h, hs, he⟩ := localSort_exec input
  have hflat := Local.runRand_compile (M := localModel) localKernel h (fun z hz => (hs z hz).1)
  refine ⟨m, Local.execRand_compile (M := localModel) localKernel h, hflat, ?_, ?_⟩
  · intro cfg hcfg
    rw [hflat] at hcfg
    obtain ⟨q, hq, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hcfg
    exact ⟨_, rfl, (pointerSortOutput_encode q.1).trans (hs q hq).2, Local.encode_heap_length q.1⟩
  · rw [ProbComp.expect_map]
    exact he

end Cslib.Algorithms.WordRAM.Quicksort
