/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.WordRAM.TrimmedYates.Basic
public import CslibFrontier.Algorithms.WordRAM.TrimmedYates.Regs
import CslibFrontier.Computability.WordRAM.CountingLoop
import CslibFrontier.Computability.WordRAM.SymbolicExec.Frame

/-!
# Bounded-cardinality subset enumeration and coordinate extraction on the word RAM

Coordinate-by-coordinate generation of subsets of size at most `k` (`prefixesUpTo`,
`genLowSubsets`), bit-scanning coordinate extraction (`extractCoords`), in-place complementation
into high-cardinality subsets of `C` (`flipHighDom`), and identity coordinate-buffer initialization
(`initIdentityCoords`).

## Main definitions

* `Cslib.Algorithms.WordRAM.TrimmedYates.prefixesUpTo`: pure coordinate-by-coordinate list of
  subsets of cardinality at most `k`.
* `Cslib.Algorithms.WordRAM.TrimmedYates.genLowSubsets`, `extractCoords`, `flipHighDom`,
  `initIdentityCoords`: Word-RAM enumeration and coordinate-preparation subroutines.

## Main results

* `Cslib.Algorithms.WordRAM.TrimmedYates.prefixesUpTo_spec`, `length_prefixesUpTo`: nodup,
  membership, and binomial-sum length characterizations of `prefixesUpTo`.
* `Cslib.Algorithms.WordRAM.TrimmedYates.exec_genLowSubsets`, `exec_extractCoords`,
  `exec_flipHighDom`, `exec_initIdentityCoords`: `ExecWithin` bounds and memory/register frames.
-/

public section

namespace Cslib.Algorithms.WordRAM.TrimmedYates

open Finset Cslib.WordRAM

/-! ### Pure model of coordinate-by-coordinate subset enumeration -/

/-- Subsets of `coords` of cardinality at most `k`, built coordinate by coordinate in the exact
order produced by `genLowSubsets`. -/
def prefixesUpTo {d : ℕ} (k : ℕ) (coords : List (Fin d)) : List (Finset (Fin d)) :=
  coords.foldl (fun acc c => acc ++ (acc.filter fun S => decide (#S < k)).map (insert c)) [∅]

private theorem prefixesUpTo_append_singleton {d : ℕ} (k : ℕ) (coords : List (Fin d)) (c : Fin d) :
    prefixesUpTo k (coords ++ [c]) =
      let prev := prefixesUpTo k coords
      prev ++ (prev.filter fun S => decide (#S < k)).map (insert c) :=
  List.foldl_append

theorem prefixesUpTo_spec {d : ℕ} (k : ℕ) :
    ∀ {coords : List (Fin d)}, coords.Nodup →
      (prefixesUpTo k coords).Nodup ∧
      ∀ S, S ∈ prefixesUpTo k coords ↔ S ⊆ coords.toFinset ∧ #S ≤ k := by
  intro coords hnd
  induction coords using List.reverseRecOn with
  | nil => simp [prefixesUpTo]
  | append_singleton coords c ih =>
    obtain ⟨hnd_prev, -, hdisj⟩ := List.nodup_append.mp hnd
    have hc_not : c ∉ coords := fun hc => hdisj c hc c (List.mem_singleton_self c) rfl
    obtain ⟨hprev_nd, hprev_mem⟩ := ih hnd_prev
    rw [prefixesUpTo_append_singleton]
    set prev := prefixesUpTo k coords
    have hc_not_in_prev : ∀ S ∈ prev, c ∉ S := fun S hS hcS =>
      hc_not (List.mem_toFinset.mp (((hprev_mem S).mp hS).1 hcS))
    have hmap_nd : ((prev.filter fun S => decide (#S < k)).map (insert c)).Nodup :=
      (hprev_nd.filter _).map_on fun S₁ h₁ S₂ h₂ heq => by
        ext x
        obtain rfl | hxc := eq_or_ne x c
        · simp [hc_not_in_prev S₁ (List.mem_filter.mp h₁).1,
            hc_not_in_prev S₂ (List.mem_filter.mp h₂).1]
        · simpa [Finset.mem_insert, hxc] using Finset.ext_iff.mp heq x
    refine ⟨List.nodup_append.mpr ⟨hprev_nd, hmap_nd, ?_⟩, fun S => ?_⟩
    · intro S₁ h₁ S₂ h₂ heq
      rcases List.mem_map.mp h₂ with ⟨T, _, rfl⟩
      exact hc_not_in_prev S₁ h₁ (heq ▸ Finset.mem_insert_self c T)
    · simp only [List.mem_append, List.mem_map, List.mem_filter, decide_eq_true_eq,
        List.toFinset_append, List.toFinset_cons, List.toFinset_nil, insert_empty_eq,
        union_singleton]
      constructor
      · rintro (hS | ⟨T, ⟨hT, hTk⟩, rfl⟩)
        · exact ⟨((hprev_mem S).mp hS).1.trans (subset_insert c _), ((hprev_mem S).mp hS).2⟩
        · rw [card_insert_of_notMem (hc_not_in_prev T hT)]
          exact ⟨insert_subset_insert c ((hprev_mem T).mp hT).1, by omega⟩
      · rintro ⟨hsub, hcard⟩
        by_cases hcS : c ∈ S
        · refine .inr ⟨S.erase c, ⟨(hprev_mem _).mpr ⟨fun x hx =>
              (Finset.mem_insert.mp (hsub (mem_of_mem_erase hx))).resolve_left
                (ne_of_mem_erase hx), card_erase_le.trans hcard⟩,
            (card_erase_lt_of_mem hcS).trans_le hcard⟩, insert_erase hcS⟩
        · exact .inl ((hprev_mem S).mpr
            ⟨fun x hx => (Finset.mem_insert.mp (hsub hx)).resolve_left fun h => hcS (h ▸ hx),
              hcard⟩)

theorem length_prefixesUpTo {d : ℕ} :
    ∀ (k : ℕ) {coords : List (Fin d)}, coords.Nodup →
      (prefixesUpTo k coords).length = ∑ j ∈ range (k + 1), coords.length.choose j := by
  intro k coords hnd
  induction coords using List.reverseRecOn generalizing k with
  | nil => simp [prefixesUpTo, Finset.sum_range_succ']
  | append_singleton coords c ih =>
    have hnd_prev : coords.Nodup := (List.nodup_append.mp hnd).1
    rw [prefixesUpTo_append_singleton]
    simp only [List.length_append, List.length_map, List.length_singleton]
    rcases k with _ | k
    · simp [ih 0 hnd_prev]
    · obtain ⟨hp_nd, hp_mem⟩ := prefixesUpTo_spec (k + 1) hnd_prev
      obtain ⟨hk_nd, hk_mem⟩ := prefixesUpTo_spec k hnd_prev
      have hflt_eq : ((prefixesUpTo (k + 1) coords).filter fun S => decide (#S < k + 1)).length =
          (prefixesUpTo k coords).length := by
        rw [← List.toFinset_card_of_nodup (hp_nd.filter _), ← List.toFinset_card_of_nodup hk_nd]
        refine congrArg Finset.card (Finset.ext fun S => ?_)
        simp only [List.mem_toFinset, List.mem_filter, hp_mem, hk_mem, decide_eq_true_eq]
        grind
      rw [hflt_eq, ih (k + 1) hnd_prev, ih k hnd_prev, Finset.sum_range_succ' _ (k + 1),
        Finset.sum_range_succ' _ (k + 1)]
      simp only [Nat.choose_zero_right]
      rw [add_right_comm, ← Finset.sum_add_distrib]
      exact congrArg (· + 1) (Finset.sum_congr rfl fun j _ =>
        by rw [add_comm, Nat.choose_succ_succ])

/-- Inner step of `genLowSubsets`: extend `xs[rGenPos]` with `rGenBitMask` when `#xs[p] < k`. -/
private def genInnerStep : Code .standard numRegs := ram[
  rGenTmp ← rGenPos + rGenPos;
  rGenTmp ← rDomPtr + rGenTmp;
  rTrieTmp ← rGenTmp + rOne;
  rTrieTmp ← *rTrieTmp;
  if rTrieTmp < rMaxCard then [
    rTrieTmp ← rTrieTmp + rOne;
    Reg.builtRoot ← rDomLen + rDomLen;
    Reg.builtRoot ← rDomPtr + Reg.builtRoot;
    Reg.builtRoot ← Reg.builtRoot + rOne;
    *Reg.builtRoot ← rTrieTmp;
    rGenTmp ← *rGenTmp;
    rGenTmp ← rGenTmp ||| rGenBitMask;
    Reg.builtRoot ← rDomLen + rDomLen;
    Reg.builtRoot ← rDomPtr + Reg.builtRoot;
    *Reg.builtRoot ← rGenTmp;
    rDomLen ← rDomLen + rOne
  ] else [
    rDomLen ← rDomLen
  ];
  rGenPos ← rGenPos + rOne ]

/-- Outer step of `genLowSubsets`: process coordinate `coords[rGenIdx]`. -/
private def genOuterStep : Code .standard numRegs :=
  .seq (ram[
    rGenTmp ← rCoordsPtr + rGenIdx;
    rGenTmp ← *rGenTmp;
    rGenBitMask ← rOne <<< rGenTmp;
    rGenOldLen ← rDomLen;
    rGenPos ← #0 ])
  (.seq (.loop (.lt rGenPos rGenOldLen) genInnerStep)
    (ram[ rGenIdx ← rGenIdx + rOne ]))

/-- Generate all subsets of `coords[0 .. rCoordsLen - 1]` of size `≤ rMaxCard` at `rDomPtr`. -/
def genLowSubsets : Code .standard numRegs :=
  .seq (ram[
    *rDomPtr ← rZero;
    rGenTmp ← rDomPtr + rOne;
    *rGenTmp ← rZero;
    rDomLen ← #1;
    rGenIdx ← #0 ])
  (.loop (.lt rGenIdx rCoordsLen) genOuterStep)

theorem genLowSubsets_preserves (i : Fin numRegs) :
    i ≠ rTrieTmp ∧ i ≠ Reg.builtRoot ∧ (i.val < 27 ∨ 33 ≤ i.val) → genLowSubsets.Preserves i := by
  decide +kernel +revert

/-- Registers that `genLowSubsets` reads and never writes. -/
private structure GenRegs (coordsPtr len k domPtr : ℕ) (s : Data numRegs) : Prop where
  zero : s.regs rZero = 0
  one : s.regs rOne = 1
  coordsPtr : s.regs rCoordsPtr = coordsPtr
  coordsLen : s.regs rCoordsLen = len
  maxCard : s.regs rMaxCard = k
  domPtr : s.regs rDomPtr = domPtr

theorem exec_genLowSubsets {w d coordsPtr domPtr k : ℕ} (coords : List (Fin d))
    (x : Data numRegs)
    (hz : x.regs rZero = 0) (ho : x.regs rOne = 1)
    (hcptr : x.regs rCoordsPtr = coordsPtr) (hclen : x.regs rCoordsLen = coords.length)
    (hk : x.regs rMaxCard = k) (hdptr : x.regs rDomPtr = domPtr)
    (hnd : coords.Nodup)
    (hcoords_mem : ∀ j (hj : j < coords.length), x.mem (coordsPtr + j) = coords[j].val)
    (hdisj : coordsPtr + coords.length ≤ domPtr)
    (hfit_mem : Fits w (domPtr + 2 * ∑ j ∈ range (k + 1), coords.length.choose j))
    (hfit_mask : Fits w (2 ^ d)) :
    let outList := prefixesUpTo k coords
    ∃ y, ExecWithin w genLowSubsets x y
        (coords.length * (20 * (∑ j ∈ range (k + 1), coords.length.choose j) + 12) + 8) ∧
      y.regs rDomLen = outList.length ∧
      HoldsDom y.mem domPtr outList ∧
      (∀ a, a < domPtr ∨ domPtr + 2 * outList.length ≤ a → y.mem a = x.mem a) ∧
      ∀ i : Fin numRegs, i ≠ rTrieTmp ∧ i ≠ Reg.builtRoot ∧ (i.val < 27 ∨ 33 ≤ i.val) →
        y.regs i = x.regs i := by
  intro outList
  set Lmax := ∑ j ∈ range (k + 1), coords.length.choose j with hLmax_def
  have hLmax_pos : 1 ≤ Lmax := by
    simp only [hLmax_def, Finset.sum_range_succ', Nat.choose_zero_right]; omega
  have hrun : ∃ y, ExecWithin w genLowSubsets x y (coords.length * (20 * Lmax + 12) + 8) ∧
      y.regs rDomLen = outList.length ∧
      HoldsDom y.mem domPtr outList ∧
      (∀ a, a < domPtr ∨ domPtr + 2 * outList.length ≤ a → y.mem a = x.mem a) := by
    let P_out (idx : ℕ) (s : Data numRegs) : Prop :=
      GenRegs coordsPtr coords.length k domPtr s ∧
      s.regs rDomLen = (prefixesUpTo k (coords.take idx)).length ∧
      HoldsDom s.mem domPtr (prefixesUpTo k (coords.take idx)) ∧
      ∀ a, a < domPtr ∨ domPtr + 2 * (prefixesUpTo k (coords.take idx)).length ≤ a →
        s.mem a = x.mem a
    have houter (s : Data numRegs) (hs : P_out (s.regs rGenIdx) s)
        (hlt : s.regs rGenIdx < coords.length) :
        ∃ z, ExecWithin w genOuterStep s z (20 * Lmax + 10) ∧
          P_out (s.regs rGenIdx + 1) z ∧ z.regs rGenIdx = s.regs rGenIdx + 1 := by
      generalize hidx : s.regs rGenIdx = idx at hs hlt ⊢
      obtain ⟨hsr, hsdlen, hsdom, hsframe⟩ := hs
      set prev := prefixesUpTo k (coords.take idx)
      let c := coords[idx]
      have hnd_take : (coords.take idx).Nodup := hnd.sublist (List.take_sublist _ _)
      have hnext_eq : prefixesUpTo k (coords.take (idx + 1)) =
          prev ++ (prev.filter fun S => decide (#S < k)).map (insert c) := by
        rw [List.take_succ_eq_append_getElem hlt, prefixesUpTo_append_singleton]
      have hnext_len_le : (prefixesUpTo k (coords.take (idx + 1))).length ≤ Lmax := by
        rw [length_prefixesUpTo k (hnd.sublist (List.take_sublist _ _)),
          List.length_take_of_le (by omega), hLmax_def]
        exact Finset.sum_le_sum fun j _ => Nat.choose_le_choose j (by omega)
      have hc_not_in_prev : ∀ S ∈ prev, c ∉ S := fun S hS hcS => by
        have hnd_app : (coords.take idx ++ [c]).Nodup :=
          List.take_succ_eq_append_getElem hlt ▸ hnd.sublist (List.take_sublist _ _)
        exact (List.nodup_append.mp hnd_app).2.2 c
          (List.mem_toFinset.mp ((((prefixesUpTo_spec k hnd_take).2 S).mp hS).1 hcS))
          c (List.mem_singleton_self c) rfl
      let accAt (p : ℕ) := prev ++ ((prev.take p).filter fun S => decide (#S < k)).map (insert c)
      have hacc_len (p : ℕ) : prev.length ≤ (accAt p).length ∧ (accAt p).length ≤ Lmax := by
        refine ⟨by simp [accAt], le_trans ?_ hnext_len_le⟩
        rw [hnext_eq]
        simp only [accAt, List.length_append, List.length_map]
        exact Nat.add_le_add_left ((List.take_sublist p prev).filter _).length_le _
      let P_in (p : ℕ) (q : Data numRegs) : Prop :=
        (GenRegs coordsPtr coords.length k domPtr q ∧ q.regs rGenOldLen = prev.length ∧
          q.regs rGenBitMask = 1 <<< c.val ∧ q.regs rGenIdx = idx) ∧
        q.regs rDomLen = (accAt p).length ∧ HoldsDom q.mem domPtr (accAt p) ∧
        ∀ a, a < domPtr ∨ domPtr + 2 * (accAt p).length ≤ a → q.mem a = x.mem a
      have hinner (q : Data numRegs) (hq : P_in (q.regs rGenPos) q)
          (hp : q.regs rGenPos < prev.length) :
          ∃ q', ExecWithin w genInnerStep q q' 18 ∧
            P_in (q.regs rGenPos + 1) q' ∧ q'.regs rGenPos = q.regs rGenPos + 1 := by
        generalize hp_eq : q.regs rGenPos = p at hq hp ⊢
        obtain ⟨hqr, hqdl, hqdom, hqframe⟩ := hq
        have hp_lt : p < (accAt p).length := (hacc_len p).1.trans_lt' hp
        have hacc_p : (accAt p)[p] = prev[p] := List.getElem_append_left hp
        obtain ⟨hmask_p, hsize_p⟩ := hqdom p hp_lt
        rw [hacc_p] at hmask_p hsize_p
        have h2p : p + p = 2 * p := by omega
        have h2l : (accAt p).length + (accAt p).length = 2 * (accAt p).length := by omega
        have hlen := (hacc_len p).2
        unfold genInnerStep
        by_cases hcard_lt : #prev[p] < k
        · have hacc1 : accAt (p + 1) = accAt p ++ [insert c prev[p]] := by
            simp only [accAt]
            rw [List.take_succ_eq_append_getElem hp, List.filter_append, List.map_append]
            simp [hcard_lt]
          have hlen1 := (hacc_len (p + 1)).2
          rw [hacc1, List.length_append, List.length_singleton] at hlen1
          have hcard : #prev[p] < 2 ^ d :=
            (card_le_univ _).trans_lt (by simpa using Nat.lt_two_pow_self)
          have hf_or : Fits w (setMask prev[p] ||| (1 <<< c.val)) := by
            rw [← setMask_insert]; exact hfit_mask.of_le (setMask_lt _).le
          wram_exec * [h2p, h2l, hmask_p, hsize_p, hcard_lt]
          refine ⟨⟨by regs_frame, ?_⟩, by wram_simp [hp_eq]⟩
          rw [hacc1]
          simp only [List.length_append, List.length_singleton]
          refine ⟨by wram_simp [hqdl], fun r hr => ?_, fun a ha => ?_⟩
          · simp only [List.length_append, List.length_singleton] at hr
            obtain hr | rfl := Nat.lt_succ_iff_lt_or_eq.mp hr
            · wram_simp [List.getElem_append_left hr]; exact hqdom r hr
            · wram_simp [List.getElem_concat_length, setMask_insert,
                card_insert_of_notMem (hc_not_in_prev _ (List.getElem_mem hp))]
          · wram_simp; exact hqframe a (by omega)
        · have hacc1 : accAt (p + 1) = accAt p := by
            simp only [accAt]
            rw [List.take_succ_eq_append_getElem hp, List.filter_append, List.map_append]
            simp [hcard_lt]
          wram_exec * [h2p, hsize_p, hcard_lt]
          refine ⟨⟨by regs_frame, ?_⟩, by wram_simp [hp_eq]⟩
          rw [hacc1]
          exact ⟨by wram_simp [hqdl], by wram_simp; exact hqdom, by wram_simp; exact hqframe⟩
      have hc_read : s.mem (coordsPtr + idx) = c.val := by
        rw [hsframe _ (Or.inl (by omega)), hcoords_mem idx hlt]
      have hbit_fit : Fits w (1 <<< c.val) := by
        rw [Nat.shiftLeft_eq, one_mul]
        exact hfit_mask.of_le (Nat.pow_le_pow_right Nat.two_pos c.isLt.le)
      unfold genOuterStep
      wram_exec * [hc_read]
      refine WP.name fun u₀ hu₀ => ?_
      have hu₀pos : u₀.regs rGenPos = 0 := by subst hu₀; wram_simp
      have hu₀P : P_in 0 u₀ := by
        subst hu₀
        have hacc0 : accAt 0 = prev := by simp [accAt]
        refine ⟨⟨by regs_frame, by wram_simp [hsdlen], by wram_simp, by wram_simp [hidx]⟩, ?_⟩
        rw [hacc0]
        exact ⟨by wram_simp [hsdlen], by wram_simp; exact hsdom, by wram_simp; exact hsframe⟩
      obtain ⟨u₁, hloop, ⟨hu₁r, hu₁dl, hu₁dom, hu₁frame⟩, -⟩ := ExecWithin.loop_count P_in
        (fun q hq => hq.1.2.1) hinner (by omega) (hu₀pos ▸ hu₀P)
      have hacc_end : accAt prev.length = prefixesUpTo k (coords.take (idx + 1)) := by
        simp only [accAt, List.take_length]; exact hnext_eq.symm
      rw [hacc_end] at hu₁dl hu₁dom hu₁frame
      have hprev_le := (hacc_len 0).1.trans (hacc_len 0).2
      refine WP.of_execWithin hloop ?_
      wram_exec *
      exact ⟨⟨by regs_frame, by wram_simp [hu₁dl], by wram_simp; exact hu₁dom,
        by wram_simp; exact hu₁frame⟩, by wram_simp⟩
    unfold genLowSubsets
    wram_exec *
    refine WP.name fun s₀ hs₀ => ?_
    have hs₀idx : s₀.regs rGenIdx = 0 := by subst hs₀; wram_simp
    have hs₀P : P_out 0 s₀ := by
      subst hs₀
      have h0 : prefixesUpTo k (coords.take 0) = [∅] := rfl
      refine ⟨by regs_frame, ?_⟩
      rw [h0]
      refine ⟨by wram_simp; rfl, fun p hp => ?_, fun a ha => ?_⟩
      · obtain rfl : p = 0 := by simpa using hp
        wram_simp; simp
      · rw [List.length_singleton] at ha
        wram_simp
    obtain ⟨y, hloop, ⟨-, hydl, hydom, hyframe⟩, -⟩ := ExecWithin.loop_count P_out
      (fun s hs => hs.1.coordsLen) houter (by omega) (hs₀idx ▸ hs₀P)
    rw [List.take_length] at hydl hydom hyframe
    refine WP.of_execWithin hloop ⟨?_, hydl, hydom, hyframe⟩
    rw [hs₀idx, Nat.sub_zero]; ring_nf; omega
  obtain ⟨y, he, hydl, hydom, hyframe⟩ := hrun
  exact ⟨y, he, hydl, hydom, hyframe, fun i hi => he.regs_eq (genLowSubsets_preserves i hi)⟩

/-- Extract set bits of `rTrieKey = setMask C` into `rCoordsPtr`, leaving `#C` in `rCoordsLen`. -/
private def extractStep : Code .standard numRegs := ram[
  rGenTmp ← rTrieRem &&& rOne;
  rTrieRem ← rTrieRem >>> rOne;
  if rZero < rGenTmp then [
    rGenTmp ← rCoordsPtr + rCoordsLen;
    *rGenTmp ← rGenIdx;
    rCoordsLen ← rCoordsLen + rOne
  ] else [
    rCoordsLen ← rCoordsLen
  ];
  rGenIdx ← rGenIdx + rOne ]

/-- Scan bits `0 .. Reg.dim - 1` of `rTrieKey` and write set indices to `rCoordsPtr`. -/
def extractCoords : Code .standard numRegs :=
  .seq (ram[ rTrieRem ← rTrieKey; rCoordsLen ← #0; rGenIdx ← #0 ])
    (.loop (.lt rGenIdx Reg.dim) extractStep)

theorem extractCoords_preserves (i : Fin numRegs) :
    i ≠ rTrieRem ∧ i ≠ rCoordsLen ∧ i ≠ rGenIdx ∧ i ≠ rGenTmp → extractCoords.Preserves i := by
  decide +kernel +revert

theorem exec_extractCoords {w d coordsPtr : ℕ} (C : Finset (Fin d)) (x : Data numRegs)
    (hz : x.regs rZero = 0) (ho : x.regs rOne = 1) (hd : x.regs Reg.dim = d)
    (hk : x.regs rTrieKey = setMask C) (hcptr : x.regs rCoordsPtr = coordsPtr)
    (hfit_mem : Fits w (coordsPtr + d)) (hfit_mask : Fits w (2 ^ d)) :
    let cList := (List.finRange d).filter (· ∈ C)
    ∃ y, ExecWithin w extractCoords x y (11 * d + 5) ∧
      y.regs rCoordsLen = cList.length ∧
      (∀ j (hj : j < cList.length), y.mem (coordsPtr + j) = cList[j].val) ∧
      (∀ a, a < coordsPtr ∨ coordsPtr + d ≤ a → y.mem a = x.mem a) ∧
      ∀ i : Fin numRegs, i ≠ rTrieRem ∧ i ≠ rCoordsLen ∧ i ≠ rGenIdx ∧ i ≠ rGenTmp →
        y.regs i = x.regs i := by
  intro cList
  have hfit_d : Fits w d := hfit_mask.of_le Nat.lt_two_pow_self.le
  let curAt (b : ℕ) := ((List.finRange d).take b).filter (· ∈ C)
  let P (b : ℕ) (s : Data numRegs) : Prop :=
    s.regs rZero = 0 ∧ s.regs rOne = 1 ∧ s.regs Reg.dim = d ∧
    s.regs rCoordsPtr = coordsPtr ∧ s.regs rCoordsLen = (curAt b).length ∧
    s.regs rTrieRem = setMask C / 2 ^ b ∧
    (∀ j (hj : j < (curAt b).length), s.mem (coordsPtr + j) = (curAt b)[j].val) ∧
    (∀ a, a < coordsPtr ∨ coordsPtr + (curAt b).length ≤ a → s.mem a = x.mem a)
  have hbody (s : Data numRegs) (hs : P (s.regs rGenIdx) s) (hb : s.regs rGenIdx < d) :
      ∃ z, ExecWithin w extractStep s z 9 ∧ P (s.regs rGenIdx + 1) z ∧
        z.regs rGenIdx = s.regs rGenIdx + 1 := by
    generalize hb_eq : s.regs rGenIdx = b at hs hb ⊢
    obtain ⟨hsz, hso, hsd, hscp, hscl, hsrem, hsmem, hsframe⟩ := hs
    set cur := curAt b
    have hcur_len_le : cur.length ≤ b := by
      calc cur.length ≤ ((List.finRange d).take b).length := List.length_filter_le _ _
        _ ≤ b := by simp
    let ib : Fin d := ⟨b, hb⟩
    have htake1 : (List.finRange d).take (b + 1) = (List.finRange d).take b ++ [ib] := by
      rw [List.take_succ_eq_append_getElem (by simp [hb])]
      simp [ib]
    have hrem_fit : Fits w (s.regs rTrieRem) := by
      rw [hsrem]; exact hfit_mask.of_le ((Nat.div_le_self _ _).trans (setMask_lt C).le)
    have hand_fit : Fits w (s.regs rTrieRem &&& 1) :=
      hfit_d.of_le (by rw [Nat.and_one_is_mod]; omega)
    have hshr_fit : Fits w (s.regs rTrieRem >>> 1) := by
      rw [Nat.shiftRight_eq_div_pow]; exact hrem_fit.of_le (Nat.div_le_self _ _)
    have hb1_fit : Fits w (b + 1) := hfit_d.of_le (by omega)
    have htb : (s.regs rTrieRem &&& 1 = 1) ↔ ib ∈ C := by
      rw [hsrem, Nat.and_one_is_mod]
      simpa [Nat.testBit_eq_decide_div_mod_eq] using testBit_setMask C ib
    have hshr_eq : s.regs rTrieRem >>> 1 = setMask C / 2 ^ (b + 1) := by
      rw [hsrem, Nat.shiftRight_eq_div_pow, pow_one, Nat.div_div_eq_div_mul, pow_succ]
    by_cases hmemC : ib ∈ C
    · have hf_addr : Fits w (coordsPtr + cur.length) := hfit_mem.of_le (by omega)
      have hf_cl1 : Fits w (cur.length + 1) := hfit_d.of_le (by omega)
      have hcur1 : curAt (b + 1) = cur ++ [ib] := by
        simp [curAt, cur, htake1, hmemC]
      wram_exec [extractStep, hsz, hso, hscp, hscl, hb_eq, htb.2 hmemC]
      dsimp only [P]
      rw [hcur1]
      simp only [List.length_append, List.length_singleton]
      refine ⟨⟨by regs_frame, by regs_frame, by regs_frame, by regs_frame, by wram_simp [hscl],
        by wram_simp [hshr_eq], fun j hj => ?_, fun a ha => ?_⟩, by wram_simp⟩
      · obtain hj | rfl := Nat.lt_succ_iff_lt_or_eq.mp hj
        · wram_simp [List.getElem_append_left hj]; exact hsmem j hj
        · wram_simp [List.getElem_concat_length, ib]
      · wram_simp; exact hsframe a (by omega)
    · have hbit0 : s.regs rTrieRem &&& 1 = 0 :=
        Nat.and_one_is_mod _ ▸ Nat.mod_two_ne_one.1 (Nat.and_one_is_mod _ ▸ mt htb.1 hmemC)
      have hcur1 : curAt (b + 1) = cur := by
        simp [curAt, cur, htake1, hmemC]
      wram_exec [extractStep, hsz, hso, hscl, hb_eq, hbit0]
      dsimp only [P]
      rw [hcur1]
      exact ⟨⟨by regs_frame, by regs_frame, by regs_frame, by regs_frame, by regs_frame,
        by wram_simp [hshr_eq], by wram_simp; exact hsmem, by wram_simp; exact hsframe⟩,
        by wram_simp⟩
  let x₀ := ((x.set rTrieRem (setMask C)).set rCoordsLen 0).set rGenIdx 0
  have hinit : ExecWithin (B := .standard) w
      (ram[ rTrieRem ← rTrieKey; rCoordsLen ← #0; rGenIdx ← #0 ]) x x₀ 3 := by
    wram_exec [hk]
  have hx₀ : P (x₀.regs rGenIdx) x₀ := by
    simp [P, curAt, x₀, hz, ho, hd, hcptr]
  obtain ⟨y, hloop, hyP, _⟩ := ExecWithin.loop_count P (fun s hs => hs.2.2.1) hbody
    (by simp [x₀]) hx₀
  obtain ⟨_, _, _, _, hycl, _, hymem, hyframe⟩ := hyP
  have hcur_d : curAt d = cList := congrArg (List.filter _) (List.take_of_length_le (by simp))
  rw [hcur_d] at hycl hymem hyframe
  have hcList_le : cList.length ≤ d := by
    calc cList.length ≤ (List.finRange d).length := List.length_filter_le _ _
      _ = d := List.length_finRange
  have he : ExecWithin w extractCoords x y (11 * d + 5) :=
    (hinit.seq hloop).mono (by simp [x₀]; omega)
  exact ⟨y, he, hycl, hymem, fun a ha => hyframe a (by omega),
    fun i hi => he.regs_eq (extractCoords_preserves i hi)⟩

/-- Flip `(Y, #Y) ↦ (C \ Y, #C - #Y)` in place at `rDomPtr` for `p < rDomLen`. -/
private def flipStep : Code .standard numRegs := ram[
  rGenTmp ← rGenPos + rGenPos;
  rGenTmp ← rDomPtr + rGenTmp;
  rTrieTmp ← *rGenTmp;
  rTrieTmp ← rTrieKey ^^^ rTrieTmp;
  *rGenTmp ← rTrieTmp;
  rGenTmp ← rGenTmp + rOne;
  rTrieTmp ← *rGenTmp;
  rTrieTmp ← rCoordsLen - rTrieTmp;
  *rGenTmp ← rTrieTmp;
  rGenPos ← rGenPos + rOne ]

/-- Complement every subset in `rDomPtr[0 .. rDomLen - 1]` inside `rTrieKey = setMask C`. -/
def flipHighDom : Code .standard numRegs :=
  .seq (ram[ rGenPos ← #0 ]) (.loop (.lt rGenPos rDomLen) flipStep)

theorem flipHighDom_preserves (i : Fin numRegs) :
    i ≠ rTrieTmp ∧ i ≠ rGenPos ∧ i ≠ rGenTmp → flipHighDom.Preserves i := by
  decide +kernel +revert

theorem exec_flipHighDom {w d domPtr : ℕ} (C : Finset (Fin d))
    (ys : List (Finset (Fin d))) (x : Data numRegs)
    (ho : x.regs rOne = 1) (hk : x.regs rTrieKey = setMask C)
    (hcl : x.regs rCoordsLen = #C) (hdptr : x.regs rDomPtr = domPtr)
    (hdlen : x.regs rDomLen = ys.length)
    (hys_sub : ∀ Y ∈ ys, Y ⊆ C) (hdom : HoldsDom x.mem domPtr ys)
    (hfit_mem : Fits w (domPtr + 2 * ys.length)) (hfit_mask : Fits w (2 ^ d)) :
    ∃ y, ExecWithin w flipHighDom x y (12 * ys.length + 3) ∧
      HoldsDom y.mem domPtr (ys.map (C \ ·)) ∧
      (∀ a, a < domPtr ∨ domPtr + 2 * ys.length ≤ a → y.mem a = x.mem a) ∧
      ∀ i : Fin numRegs, i ≠ rTrieTmp ∧ i ≠ rGenPos ∧ i ≠ rGenTmp → y.regs i = x.regs i := by
  let P (p : ℕ) (s : Data numRegs) : Prop :=
    s.regs rOne = 1 ∧ s.regs rTrieKey = setMask C ∧ s.regs rCoordsLen = #C ∧
    s.regs rDomPtr = domPtr ∧ s.regs rDomLen = ys.length ∧
    (∀ j (hj : j < ys.length), j < p →
      s.mem (domPtr + 2 * j) = setMask (C \ ys[j]) ∧
      s.mem (domPtr + 2 * j + 1) = #(C \ ys[j])) ∧
    (∀ j (hj : j < ys.length), p ≤ j →
      s.mem (domPtr + 2 * j) = setMask ys[j] ∧ s.mem (domPtr + 2 * j + 1) = #ys[j]) ∧
    (∀ a, a < domPtr ∨ domPtr + 2 * ys.length ≤ a → s.mem a = x.mem a)
  have hbody (s : Data numRegs) (hs : P (s.regs rGenPos) s) (hp : s.regs rGenPos < ys.length) :
      ∃ z, ExecWithin w flipStep s z 10 ∧ P (s.regs rGenPos + 1) z ∧
        z.regs rGenPos = s.regs rGenPos + 1 := by
    generalize hp_eq : s.regs rGenPos = p at hs hp ⊢
    obtain ⟨hso, hsk, hscl, hsdp, hsdl, hdone, htodo, hsframe⟩ := hs
    obtain ⟨hmk_p, hsz_p⟩ := htodo p hp le_rfl
    have hsub_p : ys[p] ⊆ C := hys_sub ys[p] (List.getElem_mem hp)
    have hf_xor : Fits w (setMask C ^^^ setMask ys[p]) := by
      rw [← setMask_sdiff hsub_p]; exact hfit_mask.of_le (setMask_lt _).le
    have hcard : #C ≤ d := by simpa using Finset.card_le_univ C
    have h2p : p + p = 2 * p := by omega
    wram_exec [flipStep, hso, hsk, hscl, hsdp, hp_eq, h2p, hmk_p, hsz_p]
    refine ⟨⟨by regs_frame, by regs_frame, by regs_frame, by regs_frame, by regs_frame,
      fun j hj hj' => ?_, fun j hj hj' => ?_, fun a ha => ?_⟩, by wram_simp [hp_eq]⟩
    · obtain hjp | rfl := Nat.lt_succ_iff_lt_or_eq.mp hj'
      · wram_simp; exact hdone j hj hjp
      · wram_simp [setMask_sdiff hsub_p, card_sdiff_of_subset hsub_p, hmk_p, hsz_p]
    · wram_simp; exact htodo j hj (by omega)
    · wram_simp; exact hsframe a ha
  let x₀ := x.set rGenPos 0
  have hinit : ExecWithin (B := .standard) w (ram[ rGenPos ← #0 ]) x x₀ 1 := by wram_exec
  have hx₀ : P (x₀.regs rGenPos) x₀ :=
    ⟨ho, hk, hcl, hdptr, hdlen, nofun, fun j hj _ => hdom j hj, fun _ _ => rfl⟩
  obtain ⟨y, hloop, hyP, _⟩ := ExecWithin.loop_count P (fun s hs => hs.2.2.2.2.1) hbody
    (by simp [x₀]) hx₀
  obtain ⟨_, _, _, _, _, hydone, _, hyframe⟩ := hyP
  have he : ExecWithin w flipHighDom x y (12 * ys.length + 3) :=
    (hinit.seq hloop).mono (by simp [x₀]; omega)
  exact ⟨y, he, fun j hj => by
      have hj' : j < ys.length := by simpa using hj
      simpa only [List.getElem_map] using hydone j hj' hj',
    hyframe, fun i hi => he.regs_eq (flipHighDom_preserves i hi)⟩

/-- Write `[0, 1, ..., d - 1]` (`List.finRange d`) to `rCoordsPtr[0 .. Reg.dim - 1]`. -/
private def initCoordsStep : Code .standard numRegs := ram[
  rGenTmp ← rCoordsPtr + rGenIdx;
  *rGenTmp ← rGenIdx;
  rGenIdx ← rGenIdx + rOne ]

/-- Initialize `rCoordsPtr[0 .. Reg.dim - 1]` with the identity coordinate list `[0 .. d - 1]`. -/
def initIdentityCoords : Code .standard numRegs :=
  .seq (ram[ rGenIdx ← #0 ]) (.loop (.lt rGenIdx Reg.dim) initCoordsStep)

private theorem initIdentityCoords_preserves (i : Fin numRegs) :
    i ≠ rGenIdx ∧ i ≠ rGenTmp → initIdentityCoords.Preserves i := by
  decide +kernel +revert

theorem exec_initIdentityCoords {w d coordsPtr : ℕ} (x : Data numRegs)
    (ho : x.regs rOne = 1) (hd : x.regs Reg.dim = d) (hcptr : x.regs rCoordsPtr = coordsPtr)
    (hfit_mem : Fits w (coordsPtr + d)) (hfit_d : Fits w d) :
    ∃ y, ExecWithin w initIdentityCoords x y (5 * d + 3) ∧
      (∀ j (hj : j < (List.finRange d).length),
        y.mem (coordsPtr + j) = (List.finRange d)[j].val) ∧
      (∀ a, a < coordsPtr ∨ coordsPtr + d ≤ a → y.mem a = x.mem a) ∧
      ∀ i : Fin numRegs, i ≠ rGenIdx ∧ i ≠ rGenTmp → y.regs i = x.regs i := by
  let P (b : ℕ) (s : Data numRegs) : Prop :=
    s.regs rOne = 1 ∧ s.regs Reg.dim = d ∧ s.regs rCoordsPtr = coordsPtr ∧
    (∀ j < b, s.mem (coordsPtr + j) = j) ∧
    (∀ a, a < coordsPtr ∨ coordsPtr + b ≤ a → s.mem a = x.mem a)
  have hbody (s : Data numRegs) (hs : P (s.regs rGenIdx) s) (hb : s.regs rGenIdx < d) :
      ∃ z, ExecWithin w initCoordsStep s z 3 ∧ P (s.regs rGenIdx + 1) z ∧
        z.regs rGenIdx = s.regs rGenIdx + 1 := by
    set b := s.regs rGenIdx with hb_eq
    obtain ⟨hso, hsd, hscp, hdone, hsframe⟩ := hs
    have hf_addr : Fits w (coordsPtr + b) := hfit_mem.of_le (by omega)
    have hf_b1 : Fits w (b + 1) := hfit_d.of_le (by omega)
    wram_exec [initCoordsStep, hso, hscp, hb_eq.symm]
    refine ⟨⟨by regs_frame, by regs_frame, by regs_frame, fun j hj => ?_, fun a ha => ?_⟩,
      by wram_simp⟩
    · obtain hj | rfl := Nat.lt_succ_iff_lt_or_eq.mp hj
      · wram_simp; exact hdone j hj
      · wram_simp
    · wram_simp; exact hsframe a (by omega)
  let x₀ := x.set rGenIdx 0
  have hinit : ExecWithin (B := .standard) w (ram[ rGenIdx ← #0 ]) x x₀ 1 := by wram_exec
  have hx₀ : P (x₀.regs rGenIdx) x₀ := ⟨ho, hd, hcptr, nofun, fun _ _ => rfl⟩
  obtain ⟨y, hloop, hyP, _⟩ := ExecWithin.loop_count P (fun s hs => hs.2.1) hbody
    (by simp [x₀]) hx₀
  obtain ⟨_, _, _, hydone, hyframe⟩ := hyP
  have he : ExecWithin w initIdentityCoords x y (5 * d + 3) :=
    (hinit.seq hloop).mono (by simp [x₀]; omega)
  exact ⟨y, he, fun j hj => by simpa using hydone j (by simpa using hj), hyframe,
    fun i hi => he.regs_eq (initIdentityCoords_preserves i hi)⟩

end Cslib.Algorithms.WordRAM.TrimmedYates
