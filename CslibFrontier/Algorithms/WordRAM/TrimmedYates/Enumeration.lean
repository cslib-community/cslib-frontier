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
import CslibFrontier.Computability.WordRAM.SymbolicExec

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
  intro coords
  induction coords using List.reverseRecOn with
  | nil =>
    intro _
    simp [prefixesUpTo]
  | append_singleton coords c ih =>
    intro hnd
    have hc_not : c ∉ coords := by
      intro hc
      exact (List.nodup_append.mp hnd).2.2 c hc c (by simp) rfl
    have hnd_prev : coords.Nodup := (List.nodup_append.mp hnd).1
    obtain ⟨hprev_nd, hprev_mem⟩ := ih hnd_prev
    rw [prefixesUpTo_append_singleton]
    dsimp only
    set prev := prefixesUpTo k coords
    have hc_not_in_prev : ∀ S ∈ prev, c ∉ S := fun S hS hcS =>
      hc_not (List.mem_toFinset.mp (((hprev_mem S).mp hS).1 hcS))
    have hmap_nd : ((prev.filter fun S => decide (#S < k)).map (insert c)).Nodup := by
      refine (hprev_nd.filter _).map_on ?_
      intro S₁ h₁ S₂ h₂ heq
      have h₁m := (List.mem_filter.mp h₁).1
      have h₂m := (List.mem_filter.mp h₂).1
      have h₁c := hc_not_in_prev S₁ h₁m
      have h₂c := hc_not_in_prev S₂ h₂m
      ext x
      by_cases hxc : x = c
      · subst hxc; simp [h₁c, h₂c]
      · have hx := Finset.ext_iff.mp heq x
        simpa [Finset.mem_insert, hxc] using hx
    refine ⟨List.nodup_append.mpr ⟨hprev_nd, hmap_nd, ?_⟩, fun S => ?_⟩
    · intro S₁ h₁ S₂ h₂ heq
      rcases List.mem_map.mp h₂ with ⟨T, _, rfl⟩
      exact hc_not_in_prev S₁ h₁ (heq ▸ Finset.mem_insert_self c T)
    · simp only [List.mem_append, List.mem_map, List.mem_filter, decide_eq_true_eq,
        List.toFinset_append, List.toFinset_cons, List.toFinset_nil, insert_empty_eq,
        union_singleton]
      constructor
      · rintro (hS | ⟨T, ⟨hT, hTk⟩, rfl⟩)
        · obtain ⟨hsub, hcard⟩ := (hprev_mem S).mp hS
          exact ⟨hsub.trans (subset_insert c _), hcard⟩
        · obtain ⟨hsub, _⟩ := (hprev_mem T).mp hT
          rw [card_insert_of_notMem (hc_not_in_prev T hT)]
          exact ⟨insert_subset_insert c hsub, by omega⟩
      · rintro ⟨hsub, hcard⟩
        by_cases hcS : c ∈ S
        · right
          refine ⟨S.erase c, ⟨(hprev_mem _).mpr ⟨?_, ?_⟩, ?_⟩, insert_erase hcS⟩
          · intro x hx
            have hxS := mem_of_mem_erase hx
            have hne := ne_of_mem_erase hx
            exact (Finset.mem_insert.mp (hsub hxS)).resolve_left hne
          · exact card_erase_le.trans hcard
          · rw [card_erase_of_mem hcS]
            have := Finset.card_pos.mpr ⟨c, hcS⟩
            omega
        · left
          refine (hprev_mem S).mpr ⟨fun x hx => ?_, hcard⟩
          exact (Finset.mem_insert.mp (hsub hx)).resolve_left fun h => hcS (h ▸ hx)

theorem length_prefixesUpTo {d : ℕ} :
    ∀ (k : ℕ) {coords : List (Fin d)}, coords.Nodup →
      (prefixesUpTo k coords).length = ∑ j ∈ range (k + 1), coords.length.choose j := by
  intro k coords
  induction coords using List.reverseRecOn generalizing k with
  | nil =>
    intro _
    rw [Finset.sum_range_succ']
    simp [prefixesUpTo]
  | append_singleton coords c ih =>
    intro hnd
    have hnd_prev : coords.Nodup := (List.nodup_append.mp hnd).1
    rw [prefixesUpTo_append_singleton]
    dsimp only
    rw [List.length_append, List.length_map, List.length_append, List.length_singleton]
    rcases k with _ | k
    · have hflt : (prefixesUpTo 0 coords).filter (fun S => decide (#S < 0)) = [] := by
        simp
      rw [hflt, List.length_nil, add_zero, ih 0 hnd_prev]
      simp
    · obtain ⟨hp_nd, hp_mem⟩ := prefixesUpTo_spec (k + 1) hnd_prev
      obtain ⟨hk_nd, hk_mem⟩ := prefixesUpTo_spec k hnd_prev
      have hflt_eq : ((prefixesUpTo (k + 1) coords).filter fun S => decide (#S < k + 1)).length =
          (prefixesUpTo k coords).length := by
        rw [← List.toFinset_card_of_nodup (hp_nd.filter _), ← List.toFinset_card_of_nodup hk_nd]
        congr 1
        ext S
        simp only [List.mem_toFinset, List.mem_filter, hp_mem, hk_mem, decide_eq_true_eq]
        exact ⟨fun ⟨⟨hsub, _⟩, hlt⟩ => ⟨hsub, by omega⟩,
          fun ⟨hsub, hle⟩ => ⟨⟨hsub, by omega⟩, by omega⟩⟩
      rw [hflt_eq, ih (k + 1) hnd_prev, ih k hnd_prev, Finset.sum_range_succ' _ (k + 1)]
      simp only [Nat.choose_zero_right]
      have hsum : ∑ j ∈ range (k + 1), coords.length.choose (j + 1) +
          ∑ j ∈ range (k + 1), coords.length.choose j =
          ∑ j ∈ range (k + 1), (coords.length + 1).choose (j + 1) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [add_comm, Nat.choose_succ_succ]
      rw [Finset.sum_range_succ' _ (k + 1)]
      simp only [Nat.choose_zero_right]
      omega

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
    rw [hLmax_def, Finset.sum_range_succ']
    simp only [Nat.choose_zero_right]
    omega
  have hrun : ∃ y, ExecWithin w genLowSubsets x y (coords.length * (20 * Lmax + 12) + 8) ∧
      y.regs rDomLen = outList.length ∧
      HoldsDom y.mem domPtr outList ∧
      (∀ a, a < domPtr ∨ domPtr + 2 * outList.length ≤ a → y.mem a = x.mem a) := by
    let P_out (idx : ℕ) (s : Data numRegs) : Prop :=
      s.regs rZero = 0 ∧ s.regs rOne = 1 ∧
      s.regs rCoordsPtr = coordsPtr ∧ s.regs rCoordsLen = coords.length ∧
      s.regs rMaxCard = k ∧ s.regs rDomPtr = domPtr ∧
      s.regs rDomLen = (prefixesUpTo k (coords.take idx)).length ∧
      HoldsDom s.mem domPtr (prefixesUpTo k (coords.take idx)) ∧
      ∀ a, a < domPtr ∨ domPtr + 2 * (prefixesUpTo k (coords.take idx)).length ≤ a →
        s.mem a = x.mem a
    have houter (s : Data numRegs) (hs : P_out (s.regs rGenIdx) s)
        (hlt : s.regs rGenIdx < coords.length) :
        ∃ z, ExecWithin w genOuterStep s z (20 * Lmax + 10) ∧
          P_out (s.regs rGenIdx + 1) z ∧ z.regs rGenIdx = s.regs rGenIdx + 1 := by
      generalize hidx : s.regs rGenIdx = idx at hs hlt ⊢
      dsimp only [P_out] at hs
      obtain ⟨hsz, hso, hscptr, hsclen, hsk, hsdptr, hsdlen, hsdom, hsframe⟩ := hs
      let prev := prefixesUpTo k (coords.take idx)
      change s.regs rDomLen = prev.length at hsdlen
      change HoldsDom s.mem domPtr prev at hsdom
      change ∀ a, a < domPtr ∨ domPtr + 2 * prev.length ≤ a → s.mem a = x.mem a at hsframe
      let c := coords[idx]
      have hnd_take1 : (coords.take (idx + 1)).Nodup := hnd.sublist (List.take_sublist _ _)
      have hnd_take : (coords.take idx).Nodup := hnd.sublist (List.take_sublist _ _)
      have hnext_eq : prefixesUpTo k (coords.take (idx + 1)) =
          prev ++ (prev.filter fun S => decide (#S < k)).map (insert c) := by
        rw [List.take_succ_eq_append_getElem hlt, prefixesUpTo_append_singleton]
      have hnext_len_le : (prefixesUpTo k (coords.take (idx + 1))).length ≤ Lmax := by
        rw [length_prefixesUpTo k hnd_take1, List.length_take_of_le (by omega), hLmax_def]
        exact Finset.sum_le_sum fun j _ => Nat.choose_le_choose j (by omega)
      have hprev_len_le : prev.length ≤ (prefixesUpTo k (coords.take (idx + 1))).length := by
        rw [hnext_eq, List.length_append]; omega
      have hc_not_in_prev : ∀ S ∈ prev, c ∉ S := by
        intro S hS hcS
        have hnd_app : (coords.take idx ++ [c]).Nodup := by
          rwa [← List.take_succ_eq_append_getElem hlt]
        have hc_not : c ∉ coords.take idx := fun hc =>
          (List.nodup_append.mp hnd_app).2.2 c hc c (by simp) rfl
        have hsub : S ⊆ (coords.take idx).toFinset :=
          (((prefixesUpTo_spec k hnd_take).2 S).mp hS).1
        exact hc_not (List.mem_toFinset.mp (hsub hcS))
      have hc_mem_read : s.mem (coordsPtr + idx) = c.val := by
        rw [hsframe _ (Or.inl (by omega)), hcoords_mem idx hlt]
      have hbit_fit : Fits w (1 <<< c.val) := by
        rw [Nat.shiftLeft_eq, one_mul]
        exact hfit_mask.of_le (Nat.pow_le_pow_right Nat.two_pos c.isLt.le)
      have hsetup : ∃ u₀, ExecWithin (B := .standard) w (ram[
          rGenTmp ← rCoordsPtr + rGenIdx;
          rGenTmp ← *rGenTmp;
          rGenBitMask ← rOne <<< rGenTmp;
          rGenOldLen ← rDomLen;
          rGenPos ← #0 ]) s u₀ 5 ∧
          u₀.regs rZero = 0 ∧ u₀.regs rOne = 1 ∧
          u₀.regs rCoordsPtr = coordsPtr ∧ u₀.regs rCoordsLen = coords.length ∧
          u₀.regs rMaxCard = k ∧ u₀.regs rDomPtr = domPtr ∧
          u₀.regs rDomLen = prev.length ∧ u₀.regs rGenOldLen = prev.length ∧
          u₀.regs rGenBitMask = (1 <<< c.val) ∧ u₀.regs rGenIdx = idx ∧
          u₀.regs rGenPos = 0 ∧ u₀.mem = s.mem := by
        have haddr_c : Fits w (coordsPtr + idx) := hfit_mem.of_le (by omega)
        wram_exec [hso, hscptr, hsdlen, hidx, hc_mem_read]
        wram_simp [hsz, hso, hscptr, hsclen, hsk, hsdptr, hsdlen, hidx]
      obtain ⟨u₀, hsetup_ex, hu₀z, hu₀o, hu₀cp, hu₀cl, hu₀k, hu₀dp, hu₀dl, hu₀ol,
        hu₀bm, hu₀idx, hu₀pos, hu₀mem⟩ := hsetup
      let accAt (p : ℕ) := prev ++ ((prev.take p).filter fun S => decide (#S < k)).map (insert c)
      let P_in (p : ℕ) (q : Data numRegs) : Prop :=
        q.regs rZero = 0 ∧ q.regs rOne = 1 ∧
        q.regs rCoordsPtr = coordsPtr ∧ q.regs rCoordsLen = coords.length ∧
        q.regs rMaxCard = k ∧ q.regs rDomPtr = domPtr ∧
        q.regs rGenOldLen = prev.length ∧ q.regs rGenBitMask = (1 <<< c.val) ∧
        q.regs rGenIdx = idx ∧ q.regs rDomLen = (accAt p).length ∧
        HoldsDom q.mem domPtr (accAt p) ∧
        ∀ a, a < domPtr ∨ domPtr + 2 * (accAt p).length ≤ a → q.mem a = x.mem a
      have hinner (q : Data numRegs) (hq : P_in (q.regs rGenPos) q)
          (hp : q.regs rGenPos < prev.length) :
          ∃ q', ExecWithin w genInnerStep q q' 18 ∧
            P_in (q.regs rGenPos + 1) q' ∧ q'.regs rGenPos = q.regs rGenPos + 1 := by
        generalize hp_eq : q.regs rGenPos = p at hq hp ⊢
        dsimp only [P_in] at hq
        obtain ⟨hqz, hqo, hqcp, hqcl, hqk, hqdp, hqol, hqbm, hqidx, hqdl, hqdom, hqframe⟩ := hq
        let acc := accAt p
        change q.regs rDomLen = acc.length at hqdl
        change HoldsDom q.mem domPtr acc at hqdom
        change ∀ a, a < domPtr ∨ domPtr + 2 * acc.length ≤ a → q.mem a = x.mem a at hqframe
        have hp_lt_acc : p < acc.length := by dsimp [acc, accAt]; rw [List.length_append]; omega
        have hacc_p : acc[p] = prev[p] := by dsimp [acc, accAt]; exact List.getElem_append_left hp
        obtain ⟨hmask_p, hsize_p⟩ := hqdom p hp_lt_acc
        rw [hacc_p] at hmask_p hsize_p
        have hc_not_p : c ∉ prev[p] := hc_not_in_prev prev[p] (List.getElem_mem hp)
        by_cases hcard_lt : #prev[p] < k
        · have hacc1_eq : accAt (p + 1) = acc ++ [insert c prev[p]] := by
            dsimp only [accAt, acc]
            rw [List.take_succ_eq_append_getElem hp, List.filter_append, List.map_append]
            simp [hcard_lt]
          have hacc1_len : acc.length + 1 ≤ Lmax := by
            have hle1 : (accAt (p + 1)).length ≤
                (prefixesUpTo k (coords.take (idx + 1))).length := by
              dsimp only [accAt]
              rw [hnext_eq, List.length_append, List.length_append,
                List.length_map, List.length_map]
              have := ((List.take_sublist (p + 1) prev).filter (fun S => decide (#S < k))).length_le
              omega
            rw [hacc1_eq, List.length_append, List.length_singleton] at hle1
            exact hle1.trans hnext_len_le
          have hf_2p : Fits w (p + p) := hfit_mem.of_le (by omega)
          have hf_dp2p : Fits w (domPtr + (p + p)) := hfit_mem.of_le (by omega)
          have hf_dp2p1 : Fits w (domPtr + (p + p) + 1) := hfit_mem.of_le (by omega)
          have hf_sz1 : Fits w (#prev[p] + 1) :=
            hfit_mask.of_le ((by have := Finset.card_le_univ prev[p]; simp at this; omega :
              #prev[p] + 1 ≤ d + 1).trans (by
              have := Nat.lt_two_pow_self (n := d); omega))
          have hf_2l : Fits w (acc.length + acc.length) := hfit_mem.of_le (by omega)
          have hf_dp2l : Fits w (domPtr + (acc.length + acc.length)) := hfit_mem.of_le (by omega)
          have hf_dp2l1 : Fits w (domPtr + (acc.length + acc.length) + 1) :=
            hfit_mem.of_le (by omega)
          have hf_or : Fits w (setMask prev[p] ||| (1 <<< c.val)) := by
            rw [← setMask_insert]; exact hfit_mask.of_le (setMask_lt _).le
          have hf_l1 : Fits w (acc.length + 1) := hfit_mem.of_le (by omega)
          have hf_p1 : Fits w (p + 1) := hfit_mem.of_le (by omega)
          have h2p_eq : p + p = 2 * p := by omega
          have h2l_eq : acc.length + acc.length = 2 * acc.length := by omega
          have hread_sz : q.mem (domPtr + (p + p) + 1) = #prev[p] := by
            simpa only [h2p_eq] using hsize_p
          have hread_mk : q.mem (domPtr + (p + p)) = setMask prev[p] := by
            simpa only [h2p_eq] using hmask_p
          have hstep : ∃ q', ExecWithin w genInnerStep q q' 18 ∧
              q'.regs rZero = 0 ∧ q'.regs rOne = 1 ∧
              q'.regs rCoordsPtr = coordsPtr ∧ q'.regs rCoordsLen = coords.length ∧
              q'.regs rMaxCard = k ∧ q'.regs rDomPtr = domPtr ∧
              q'.regs rGenOldLen = prev.length ∧ q'.regs rGenBitMask = (1 <<< c.val) ∧
              q'.regs rGenIdx = idx ∧ q'.regs rDomLen = acc.length + 1 ∧
              q'.regs rGenPos = p + 1 ∧
              q'.mem = Function.update
                (Function.update q.mem (domPtr + 2 * acc.length + 1) (#prev[p] + 1))
                (domPtr + 2 * acc.length) (setMask (insert c prev[p])) := by
            unfold genInnerStep
            wram_exec [hqo, hqk, hqdp, hqdl, hqbm, hp_eq, hread_sz, hcard_lt, hread_mk]
            refine ⟨hqz, hqo, hqcp, hqcl, hqk, hqdp, hqol, hqbm, hqidx, ?_, ?_, ?_⟩
            · wram_simp [hqdl]
            · wram_simp [hp_eq]
            · wram_simp [h2l_eq, hread_mk, setMask_insert]
          obtain ⟨q', hq'_ex, hq'z, hq'o, hq'cp, hq'cl, hq'k, hq'dp, hq'ol, hq'bm,
            hq'idx, hq'dl, hq'pos, hq'mem⟩ := hstep
          refine ⟨q', hq'_ex, ?_, hq'pos⟩
          dsimp only [P_in]
          rw [hacc1_eq]
          refine ⟨hq'z, hq'o, hq'cp, hq'cl, hq'k, hq'dp, hq'ol, hq'bm, hq'idx,
            by rw [hq'dl]; simp [acc], ?_, ?_⟩
          · intro r hr
            rw [List.length_append, List.length_singleton] at hr
            by_cases hr_eq : r = acc.length
            · subst hr_eq
              simp only [List.getElem_append_right (le_rfl), Nat.sub_self, List.getElem_singleton,
                hq'mem, card_insert_of_notMem hc_not_p]
              refine ⟨Function.update_self _ _ _, ?_⟩
              rw [Function.update_of_ne (by omega), Function.update_self]
            · have hr_lt : r < acc.length := by omega
              simp only [List.getElem_append_left hr_lt, hq'mem]
              refine ⟨?_, ?_⟩
              · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
                exact (hqdom r hr_lt).1
              · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
                exact (hqdom r hr_lt).2
          · intro a ha
            rw [List.length_append, List.length_singleton] at ha
            rw [hq'mem, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            exact hqframe a (by omega)
        · have hacc1_eq : accAt (p + 1) = acc := by
            dsimp only [accAt, acc]
            rw [List.take_succ_eq_append_getElem hp, List.filter_append, List.map_append]
            simp [hcard_lt]
          have hprev_le : prev.length ≤ Lmax := hprev_len_le.trans hnext_len_le
          have hf_2p : Fits w (p + p) := hfit_mem.of_le (by omega)
          have hf_dp2p : Fits w (domPtr + (p + p)) := hfit_mem.of_le (by omega)
          have hf_dp2p1 : Fits w (domPtr + (p + p) + 1) := hfit_mem.of_le (by omega)
          have hf_p1 : Fits w (p + 1) := hfit_mem.of_le (by omega)
          have h2p_eq : p + p = 2 * p := by omega
          have hread_sz : q.mem (domPtr + (p + p) + 1) = #prev[p] := by
            simpa only [h2p_eq] using hsize_p
          have hstep : ∃ q', ExecWithin w genInnerStep q q' 18 ∧
              q'.regs rZero = 0 ∧ q'.regs rOne = 1 ∧
              q'.regs rCoordsPtr = coordsPtr ∧ q'.regs rCoordsLen = coords.length ∧
              q'.regs rMaxCard = k ∧ q'.regs rDomPtr = domPtr ∧
              q'.regs rGenOldLen = prev.length ∧ q'.regs rGenBitMask = (1 <<< c.val) ∧
              q'.regs rGenIdx = idx ∧ q'.regs rDomLen = acc.length ∧
              q'.regs rGenPos = p + 1 ∧ q'.mem = q.mem := by
            unfold genInnerStep
            wram_exec [hqo, hqk, hqdp, hqdl, hp_eq, hread_sz, hcard_lt]
            wram_simp [hqz, hqo, hqcp, hqcl, hqk, hqdp, hqol, hqbm, hqidx, hqdl, hp_eq]
          obtain ⟨q', hq'_ex, hq'z, hq'o, hq'cp, hq'cl, hq'k, hq'dp, hq'ol, hq'bm,
            hq'idx, hq'dl, hq'pos, hq'mem⟩ := hstep
          refine ⟨q', hq'_ex, ?_, hq'pos⟩
          dsimp only [P_in]
          rw [hacc1_eq, hq'mem]
          exact ⟨hq'z, hq'o, hq'cp, hq'cl, hq'k, hq'dp, hq'ol, hq'bm, hq'idx, hq'dl, hqdom, hqframe⟩
      have hu₀_in : P_in (u₀.regs rGenPos) u₀ := by
        dsimp only [P_in, accAt]
        rw [hu₀pos, List.take_zero, List.filter_nil, List.map_nil, List.append_nil, hu₀mem]
        exact ⟨hu₀z, hu₀o, hu₀cp, hu₀cl, hu₀k, hu₀dp, hu₀ol, hu₀bm, hu₀idx, hu₀dl, hsdom, hsframe⟩
      obtain ⟨u₁, hloop_in, hu₁P, _⟩ := ExecWithin.loop_count P_in
        (fun q hq => hq.2.2.2.2.2.2.1) hinner (by simp [hu₀pos]) hu₀_in
      obtain ⟨hu₁z, hu₁o, hu₁cp, hu₁cl, hu₁k, hu₁dp, _, _, hu₁idx, hu₁dl, hu₁dom, hu₁frame⟩ := hu₁P
      dsimp only [accAt] at hu₁dl hu₁dom hu₁frame
      rw [List.take_length, ← hnext_eq] at hu₁dl hu₁dom hu₁frame
      have hf_idx1 : Fits w (idx + 1) := hfit_mem.of_le (by omega)
      let z := u₁.set rGenIdx (idx + 1)
      have hinc : ExecWithin (B := .standard) w (ram[ rGenIdx ← rGenIdx + rOne ]) u₁ z 1 := by
        wram_exec [hu₁idx, hu₁o]
      have hprev_le_Lmax : prev.length ≤ Lmax := hprev_len_le.trans hnext_len_le
      have hmul_le : 20 * prev.length ≤ 20 * Lmax := Nat.mul_le_mul_left 20 hprev_le_Lmax
      have hcost : 5 + ((prev.length - u₀.regs rGenPos) * (18 + 2) + 2) + 1 ≤ 20 * Lmax + 10 := by
        rw [hu₀pos, Nat.sub_zero, Nat.mul_comm _ 20]
        omega
      refine ⟨z, (hsetup_ex.seq (hloop_in.seq hinc)).mono hcost, ?_, by simp [z]⟩
      dsimp only [P_out]
      exact ⟨by simp [z, hu₁z], by simp [z, hu₁o], by simp [z, hu₁cp], by simp [z, hu₁cl],
        by simp [z, hu₁k], by simp [z, hu₁dp], by simp [z, hu₁dl], hu₁dom, hu₁frame⟩
    have hf_dp1 : Fits w (domPtr + 1) := hfit_mem.of_le (by omega)
    have hinit : ∃ s₀, ExecWithin (B := .standard) w (ram[
        *rDomPtr ← rZero;
        rGenTmp ← rDomPtr + rOne;
        *rGenTmp ← rZero;
        rDomLen ← #1;
        rGenIdx ← #0 ]) x s₀ 5 ∧
        s₀.regs rZero = 0 ∧ s₀.regs rOne = 1 ∧
        s₀.regs rCoordsPtr = coordsPtr ∧ s₀.regs rCoordsLen = coords.length ∧
        s₀.regs rMaxCard = k ∧ s₀.regs rDomPtr = domPtr ∧
        s₀.regs rDomLen = 1 ∧ s₀.regs rGenIdx = 0 ∧
        s₀.mem = Function.update (Function.update x.mem domPtr 0) (domPtr + 1) 0 := by
      wram_exec [hz, ho, hdptr]
      wram_simp [hz, ho, hcptr, hclen, hk, hdptr]
    obtain ⟨s₀, hinit_ex, hs₀z, hs₀o, hs₀cp, hs₀cl, hs₀k, hs₀dp, hs₀dl, hs₀idx, hs₀mem⟩ := hinit
    have hs₀P : P_out (s₀.regs rGenIdx) s₀ := by
      dsimp only [P_out]
      rw [hs₀idx, List.take_zero]
      refine ⟨hs₀z, hs₀o, hs₀cp, hs₀cl, hs₀k, hs₀dp, hs₀dl, ?_, ?_⟩
      · intro p hp
        obtain rfl : p = 0 := by simp [prefixesUpTo] at hp; omega
        simp [prefixesUpTo, hs₀mem]
      · intro a ha
        simp only [prefixesUpTo, List.foldl_nil, List.length_singleton] at ha
        rw [hs₀mem, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    obtain ⟨y, hloop_out, hyP, _⟩ := ExecWithin.loop_count P_out
      (fun s hs => hs.2.2.2.1) houter (by simp [hs₀idx]) hs₀P
    obtain ⟨_, _, _, _, _, _, hydl, hydom, hyframe⟩ := hyP
    rw [List.take_length] at hydl hydom hyframe
    refine ⟨y, (hinit_ex.seq hloop_out).mono (by
      rw [hs₀idx, Nat.sub_zero]
      change 5 + (coords.length * (20 * Lmax + 12) + 2) ≤ coords.length * (20 * Lmax + 12) + 8
      omega),
      hydl, hydom, hyframe⟩
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
  have hrun : ∃ y, ExecWithin w extractCoords x y (11 * d + 5) ∧
      y.regs rCoordsLen = cList.length ∧
      (∀ j (hj : j < cList.length), y.mem (coordsPtr + j) = cList[j].val) ∧
      (∀ a, a < coordsPtr ∨ coordsPtr + d ≤ a → y.mem a = x.mem a) := by
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
      dsimp only [P] at hs
      obtain ⟨hsz, hso, hsd, hscp, hscl, hsrem, hsmem, hsframe⟩ := hs
      let cur := curAt b
      change s.regs rCoordsLen = cur.length at hscl
      change ∀ j (hj : j < cur.length), s.mem (coordsPtr + j) = cur[j].val at hsmem
      change ∀ a, a < coordsPtr ∨ coordsPtr + cur.length ≤ a → s.mem a = x.mem a at hsframe
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
      have hbit_iff : s.regs rTrieRem &&& 1 = (if ib ∈ C then 1 else 0) := by
        rw [hsrem, Nat.and_one_is_mod]
        have htb := testBit_setMask C ib
        rw [Nat.testBit_eq_decide_div_mod_eq, decide_eq_decide] at htb
        change setMask C / 2 ^ b % 2 = if ib ∈ C then 1 else 0
        have hmod2 : setMask C / 2 ^ b % 2 < 2 := Nat.mod_lt _ Nat.two_pos
        by_cases hmemC : ib ∈ C
        · simp only [hmemC, ↓reduceIte]; exact htb.mpr hmemC
        · have h0 : setMask C / 2 ^ b % 2 ≠ 1 := mt htb.mp hmemC
          simp only [hmemC, ↓reduceIte]; omega
      have hshr_eq : s.regs rTrieRem >>> 1 = setMask C / 2 ^ (b + 1) := by
        rw [hsrem, Nat.shiftRight_eq_div_pow, pow_one, Nat.div_div_eq_div_mul, pow_succ]
      by_cases hmemC : ib ∈ C
      · have hbit1 : s.regs rTrieRem &&& 1 = 1 := by simp [hbit_iff, hmemC]
        have hf_addr : Fits w (coordsPtr + cur.length) := hfit_mem.of_le (by omega)
        have hf_cl1 : Fits w (cur.length + 1) := hfit_d.of_le (by omega)
        have hcur1 : curAt (b + 1) = cur ++ [ib] := by
          dsimp only [curAt, cur]
          rw [htake1, List.filter_append, List.filter_cons_of_pos (by simp [hmemC]),
            List.filter_nil]
        have hstep : ∃ z, ExecWithin w extractStep s z 9 ∧
            z.regs rZero = 0 ∧ z.regs rOne = 1 ∧ z.regs Reg.dim = d ∧
            z.regs rCoordsPtr = coordsPtr ∧ z.regs rCoordsLen = cur.length + 1 ∧
            z.regs rTrieRem = setMask C / 2 ^ (b + 1) ∧ z.regs rGenIdx = b + 1 ∧
            z.mem = Function.update s.mem (coordsPtr + cur.length) b := by
          unfold extractStep
          wram_exec [hsz, hso, hscp, hscl, hb_eq, hbit1]
          wram_simp [hsz, hso, hsd, hscp, hscl, hb_eq, hshr_eq]
        obtain ⟨z, hz_ex, hzz, hzo, hzd, hzcp, hzcl, hzrem, hzidx, hzmem⟩ := hstep
        refine ⟨z, hz_ex, ?_, hzidx⟩
        dsimp only [P]
        rw [hcur1]
        refine ⟨hzz, hzo, hzd, hzcp, by simp [hzcl], hzrem, ?_, ?_⟩
        · intro j hj
          rw [List.length_append, List.length_singleton] at hj
          by_cases hj_eq : j = cur.length
          · subst hj_eq
            simp [hzmem, ib]
          · have hj_lt : j < cur.length := by omega
            rw [List.getElem_append_left hj_lt, hzmem, Function.update_of_ne (by omega)]
            exact hsmem j hj_lt
        · intro a ha
          rw [List.length_append, List.length_singleton] at ha
          rw [hzmem, Function.update_of_ne (by omega)]
          exact hsframe a (by omega)
      · have hbit0 : s.regs rTrieRem &&& 1 = 0 := by simp [hbit_iff, hmemC]
        have hcur1 : curAt (b + 1) = cur := by
          dsimp only [curAt, cur]
          rw [htake1, List.filter_append, List.filter_cons_of_neg (by simp [hmemC]),
            List.filter_nil, List.append_nil]
        have hstep : ∃ z, ExecWithin w extractStep s z 9 ∧
            z.regs rZero = 0 ∧ z.regs rOne = 1 ∧ z.regs Reg.dim = d ∧
            z.regs rCoordsPtr = coordsPtr ∧ z.regs rCoordsLen = cur.length ∧
            z.regs rTrieRem = setMask C / 2 ^ (b + 1) ∧ z.regs rGenIdx = b + 1 ∧
            z.mem = s.mem := by
          unfold extractStep
          wram_exec [hsz, hso, hscl, hb_eq, hbit0]
          wram_simp [hsz, hso, hsd, hscp, hscl, hb_eq, hshr_eq]
        obtain ⟨z, hz_ex, hzz, hzo, hzd, hzcp, hzcl, hzrem, hzidx, hzmem⟩ := hstep
        refine ⟨z, hz_ex, ?_, hzidx⟩
        dsimp only [P]
        rw [hcur1, hzmem]
        exact ⟨hzz, hzo, hzd, hzcp, hzcl, hzrem, hsmem, hsframe⟩
    let x₀ := ((x.set rTrieRem (setMask C)).set rCoordsLen 0).set rGenIdx 0
    have hinit : ExecWithin (B := .standard) w
        (ram[ rTrieRem ← rTrieKey; rCoordsLen ← #0; rGenIdx ← #0 ]) x x₀ 3 := by
      wram_exec [hk]
    have hx₀ : P (x₀.regs rGenIdx) x₀ := by
      dsimp only [P, curAt]
      simp [x₀, hz, ho, hd, hcptr]
    obtain ⟨y, hloop, hyP, _⟩ := ExecWithin.loop_count P (fun s hs => hs.2.2.1) hbody
      (by simp [x₀]) hx₀
    obtain ⟨_, _, _, _, hycl, _, hymem, hyframe⟩ := hyP
    have hcur_d : curAt d = cList := by
      dsimp only [curAt, cList]
      rw [List.take_of_length_le (by simp)]
    rw [hcur_d] at hycl hymem hyframe
    have hcList_le : cList.length ≤ d := by
      calc cList.length ≤ (List.finRange d).length := List.length_filter_le _ _
        _ = d := List.length_finRange
    refine ⟨y, (hinit.seq hloop).mono (by simp [x₀]; omega), hycl, hymem,
      fun a ha => hyframe a (by omega)⟩
  obtain ⟨y, he, hycl, hymem, hyframe⟩ := hrun
  exact ⟨y, he, hycl, hymem, hyframe, fun i hi => he.regs_eq (extractCoords_preserves i hi)⟩

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
  have hrun : ∃ y, ExecWithin w flipHighDom x y (12 * ys.length + 3) ∧
      HoldsDom y.mem domPtr (ys.map (C \ ·)) ∧
      (∀ a, a < domPtr ∨ domPtr + 2 * ys.length ≤ a → y.mem a = x.mem a) := by
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
      dsimp only [P] at hs
      obtain ⟨hso, hsk, hscl, hsdp, hsdl, hdone, htodo, hsframe⟩ := hs
      obtain ⟨hmk_p, hsz_p⟩ := htodo p hp le_rfl
      have hsub_p : ys[p] ⊆ C := hys_sub ys[p] (List.getElem_mem hp)
      have hf_2p : Fits w (p + p) := hfit_mem.of_le (by omega)
      have hf_dp2p : Fits w (domPtr + (p + p)) := hfit_mem.of_le (by omega)
      have hf_dp2p1 : Fits w (domPtr + (p + p) + 1) := hfit_mem.of_le (by omega)
      have hf_xor : Fits w (setMask C ^^^ setMask ys[p]) := by
        rw [← setMask_sdiff hsub_p]; exact hfit_mask.of_le (setMask_lt _).le
      have hf_sub : Fits w (#C - #ys[p]) :=
        hfit_mask.of_le ((by have := Finset.card_le_univ C; simp at this; omega :
          #C - #ys[p] ≤ d).trans Nat.lt_two_pow_self.le)
      have hf_p1 : Fits w (p + 1) := hfit_mem.of_le (by omega)
      have h2p_eq : p + p = 2 * p := by omega
      have hrmk : s.mem (domPtr + (p + p)) = setMask ys[p] := by simpa only [h2p_eq] using hmk_p
      have hrsz : s.mem (domPtr + (p + p) + 1) = #ys[p] := by simpa only [h2p_eq] using hsz_p
      have hstep : ∃ z, ExecWithin w flipStep s z 10 ∧
          z.regs rOne = 1 ∧ z.regs rTrieKey = setMask C ∧ z.regs rCoordsLen = #C ∧
          z.regs rDomPtr = domPtr ∧ z.regs rDomLen = ys.length ∧ z.regs rGenPos = p + 1 ∧
          z.mem = Function.update
            (Function.update s.mem (domPtr + 2 * p) (setMask (C \ ys[p])))
            (domPtr + 2 * p + 1) #(C \ ys[p]) := by
        unfold flipStep
        wram_exec [hso, hsk, hscl, hsdp, hp_eq, hrmk, hrsz]
        refine ⟨hso, hsk, hscl, hsdp, hsdl, ?_, ?_⟩
        · wram_simp [hp_eq]
        · wram_simp [h2p_eq, hrmk, hrsz, setMask_sdiff hsub_p, Finset.card_sdiff_of_subset hsub_p]
      obtain ⟨z, hz_ex, hzo, hzk, hzcl, hzdp, hzdl, hzpos, hzmem⟩ := hstep
      refine ⟨z, hz_ex, ⟨hzo, hzk, hzcl, hzdp, hzdl, ?_, ?_, ?_⟩, hzpos⟩
      · intro j hj hlt_j
        by_cases hjp : j = p
        · subst hjp
          simp only [hzmem]
          exact ⟨by rw [Function.update_of_ne (by omega), Function.update_self],
            Function.update_self _ _ _⟩
        · simp only [hzmem]
          refine ⟨?_, ?_⟩
          · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            exact (hdone j hj (by omega)).1
          · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            exact (hdone j hj (by omega)).2
      · intro j hj hle
        simp only [hzmem]
        refine ⟨?_, ?_⟩
        · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          exact (htodo j hj (by omega)).1
        · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          exact (htodo j hj (by omega)).2
      · intro a ha
        rw [hzmem, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact hsframe a ha
    let x₀ := x.set rGenPos 0
    have hinit : ExecWithin (B := .standard) w (ram[ rGenPos ← #0 ]) x x₀ 1 := by wram_exec
    have hx₀ : P (x₀.regs rGenPos) x₀ := by
      refine ⟨by simp [x₀, ho], by simp [x₀, hk], by simp [x₀, hcl], by simp [x₀, hdptr],
        by simp [x₀, hdlen], by simp [x₀], fun j hj _ => hdom j hj, fun _ _ => rfl⟩
    obtain ⟨y, hloop, hyP, _⟩ := ExecWithin.loop_count P (fun s hs => hs.2.2.2.2.1) hbody
      (by simp [x₀]) hx₀
    obtain ⟨_, _, _, _, _, hydone, _, hyframe⟩ := hyP
    refine ⟨y, (hinit.seq hloop).mono (by simp [x₀]; omega), ?_, hyframe⟩
    intro j hj
    rw [List.length_map] at hj
    simpa only [List.getElem_map] using hydone j hj hj
  obtain ⟨y, he, hydom, hyframe⟩ := hrun
  exact ⟨y, he, hydom, hyframe, fun i hi => he.regs_eq (flipHighDom_preserves i hi)⟩

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
  have hrun : ∃ y, ExecWithin w initIdentityCoords x y (5 * d + 3) ∧
      (∀ j (hj : j < d), y.mem (coordsPtr + j) = j) ∧
      (∀ a, a < coordsPtr ∨ coordsPtr + d ≤ a → y.mem a = x.mem a) := by
    let P (b : ℕ) (s : Data numRegs) : Prop :=
      s.regs rOne = 1 ∧ s.regs Reg.dim = d ∧ s.regs rCoordsPtr = coordsPtr ∧
      (∀ j < b, s.mem (coordsPtr + j) = j) ∧
      (∀ a, a < coordsPtr ∨ coordsPtr + b ≤ a → s.mem a = x.mem a)
    have hbody (s : Data numRegs) (hs : P (s.regs rGenIdx) s) (hb : s.regs rGenIdx < d) :
        ∃ z, ExecWithin w initCoordsStep s z 3 ∧ P (s.regs rGenIdx + 1) z ∧
          z.regs rGenIdx = s.regs rGenIdx + 1 := by
      generalize hb_eq : s.regs rGenIdx = b at hs hb ⊢
      obtain ⟨hso, hsd, hscp, hdone, hsframe⟩ := hs
      have hf_addr : Fits w (coordsPtr + b) := hfit_mem.of_le (by omega)
      have hf_b1 : Fits w (b + 1) := hfit_d.of_le (by omega)
      have hst : ∃ z, ExecWithin w initCoordsStep s z 3 ∧
          z.regs rOne = 1 ∧ z.regs Reg.dim = d ∧ z.regs rCoordsPtr = coordsPtr ∧
          z.regs rGenIdx = b + 1 ∧ z.mem = Function.update s.mem (coordsPtr + b) b := by
        unfold initCoordsStep
        wram_exec [hso, hscp, hb_eq]
        wram_simp [hso, hsd, hscp, hb_eq]
      obtain ⟨z, hez, hzo, hzd, hzcp, hzb, hzm⟩ := hst
      refine ⟨z, hez, ⟨hzo, hzd, hzcp, ?_, ?_⟩, hzb⟩
      · intro j hj
        by_cases hjb : j = b
        · subst hjb; simp [hzm]
        · rw [hzm, Function.update_of_ne (by omega)]; exact hdone j (by omega)
      · intro a ha
        rw [hzm, Function.update_of_ne (by omega)]; exact hsframe a (by omega)
    let x₀ := x.set rGenIdx 0
    have hinit : ExecWithin (B := .standard) w (ram[ rGenIdx ← #0 ]) x x₀ 1 := by wram_exec
    have hx₀ : P (x₀.regs rGenIdx) x₀ :=
      ⟨by simp [x₀, ho], by simp [x₀, hd], by simp [x₀, hcptr],
       by simp [x₀], fun _ _ => rfl⟩
    obtain ⟨y, hloop, hyP, _⟩ := ExecWithin.loop_count P (fun s hs => hs.2.1) hbody
      (by simp [x₀]) hx₀
    obtain ⟨_, _, _, hydone, hyframe⟩ := hyP
    exact ⟨y, (hinit.seq hloop).mono (by simp [x₀]; omega), hydone, hyframe⟩
  obtain ⟨y, he, hydone, hyframe⟩ := hrun
  refine ⟨y, he, fun j hj => ?_, hyframe,
    fun i hi => he.regs_eq (initIdentityCoords_preserves i hi)⟩
  rw [List.length_finRange] at hj
  simpa using hydone j hj

end Cslib.Algorithms.WordRAM.TrimmedYates
