/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ThreeSum.Frontend.Bounds
import CslibFrontier.Computability.WordRAM.SymbolicExec.CanonicalCall

/-!
# Exact native frontend from initialized signed input

The header is the unsigned length; payload cell one starts the canonical signed encoding.
The parameter program computes the magnitude and explicit radix bit count. The radix program
preserves full multiplicities; the complete descriptor program enumerates the existing inputs.

## Main results

* `exec_input`: complete initialized-input execution, exact descriptors and full multiplicities.
* `construct_preserves_parameters`: computed parameters remain available to the traversal caller.

Execution uses a positive logarithmic physical width and fixed code per exponent.
-/

public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.Frontend

open Cslib.WordRAM

theorem parameterRegisters_injective : Function.Injective parameterRegisters := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  dsimp only [parameterRegisters] at this
  omega

theorem radixRegisters_injective : Function.Injective radixRegisters := by
  intro i j h
  exact Fin.ext (congrArg (fun z : Fin 128 => z.val) h)

theorem arrayRegisters_injective : Function.Injective arrayRegisters := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  dsimp only [arrayRegisters] at this
  omega

/-- Parameter outputs remain available to the parent traversal without recomputation. -/
theorem construct_preserves_parameters (i : Fin 24) :
    construct.Preserves (parameterRegisters i) := by
  fin_cases i <;> decide

private theorem cost_sum_bound (p r A n k : ℕ) (hk : k ≤ n) :
    p + (4 + (r + (9 + (A * (43 * k + 32) + 21 + 3)))) ≤
      p + r + A * (43 * n + 32) + 38 - 1 := by
  have := Nat.mul_le_mul_left A (show 43 * k + 32 ≤ 43 * n + 32 by omega)
  omega

/-- Complete initialized-input native construction, with no supplied algorithm or fit advice. -/
theorem exec_input {κ w : ℕ} (input : List ℤ) (hw : width κ input.length ≤ w)
    (hvalues : ∀ z ∈ input, |z| ≤ ((input.length + 2) ^ κ : ℕ)) :
    ∃ (y : Data 128) (rs : List (ℕ × ℕ)),
      ExecWithin w (program κ) (Data.init (input.map Signed.encode)) y (cost κ input.length - 1) ∧
      Output (layout κ input.length) ((input.length + 2) ^ κ) rs y.mem ∧
      y.regs descriptorBase = (layout κ input.length).descriptors ∧
      y.regs descriptorCount = (layout κ input.length).count ∧
      y.regs heapEnd = (layout κ input.length).endpoint ∧
      (rs.map Prod.fst).Nodup ∧ (rs.map Prod.fst).Pairwise (· < ·) ∧
      (∀ k, k ∈ rs.map Prod.fst ↔ k ∈ input.map Signed.encode) ∧
      (∀ p ∈ rs, 0 < p.2 ∧ (input.map Signed.encode).count p.1 = p.2) ∧
      Block.HoldsList (1 + 2 * input.length) (rs.map Prod.fst) y.mem ∧
      Block.HoldsList (1 + 3 * input.length) (rs.map Prod.snd) y.mem ∧
      ChanHe.Parameters.Output input.length ((input.length + 2) ^ κ)
        (y.comap parameterRegisters) ∧
      Modifies (Block.mk 1 ((layout κ input.length).endpoint - 1)).footprint
        (Data.init (input.map Signed.encode) : Data 128).mem y.mem := by
  let n := input.length
  let U := (n + 2) ^ κ
  let l := layout κ n
  let x : Data 128 := Data.init (input.map Signed.encode)
  have hparam : ChanHe.Parameters.width κ n ≤ w := by dsimp only [width, n] at hw ⊢; omega
  have hp := ChanHe.Parameters.budget_fits hparam
  have hfront := array_budget_fits hw
  have hN : Fits w (1 + 4 * n) := hp.of_le (by
    dsimp only [ChanHe.Parameters.Math.budget]; omega)
  have h2 : Fits w 2 := hp.of_le (by dsimp only [ChanHe.Parameters.Math.budget]; omega)
  have hB : Fits w l.digits := hp.of_le (by
    have hl := Nat.log_le_self 2 (4 * U)
    change Cslib.Algorithms.ThreeSum.labelBits (2 * U) ≤ ChanHe.Parameters.Math.budget n U
    dsimp only [Cslib.Algorithms.ThreeSum.labelBits, ChanHe.Parameters.Math.budget]
    rw [show 2 * (2 * U) = 4 * U by omega]
    omega)
  have hU : 1 ≤ U := Nat.one_le_pow _ _ (by omega)
  obtain ⟨a, ha, ⟨hop, ham⟩, _⟩ := ExecWithin.rename_post parameterRegisters_injective
    (ChanHe.Parameters.exec κ (x.comap parameterRegisters)
      (by simpa only [Data.comap_mem, x, Data.init_mem_zero, List.length_map] using hp))
  simp only [Data.comap_mem, x, Data.init_mem_zero, List.length_map] at ha hop
  simp only [Data.comap_mem] at ham
  have han : a.regs (parameterRegisters ChanHe.Parameters.len) = n := hop.len
  have haU : a.regs (parameterRegisters ChanHe.Parameters.magnitude) = U := hop.magnitude
  have haB : a.regs (parameterRegisters ChanHe.Parameters.digits) = l.digits := hop.digits
  obtain ⟨b, hb, hbm, hb_len, hb_src, hb_dst, hb_bits, hb_high⟩ :
      ∃ b, ExecWithin w radixSetup a b 4 ∧ b.mem = a.mem ∧
        (b.comap radixRegisters).regs RadixSort.len = n ∧
        (b.comap radixRegisters).regs RadixSort.src = 1 ∧
        (b.comap radixRegisters).regs RadixSort.dst = n + 1 ∧
        (b.comap radixRegisters).regs RadixSort.bits = l.digits ∧
        (∀ i, b.regs (parameterRegisters i) = a.regs (parameterRegisters i)) := by
    unfold radixSetup
    wram_exec [han, haB]
    refine ⟨rfl, by wram_simp, by wram_simp, by wram_simp, by wram_simp, fun i => ?_⟩
    have hne (j : Fin 16) : parameterRegisters i ≠ radixRegisters j := by
      intro he; have := congrArg Fin.val he; dsimp only [parameterRegisters, radixRegisters] at this
      omega
    simp only [Data.set_regs, Function.update_of_ne (hne _)]
  have hmem : Block.HoldsList 1 (input.map Signed.encode) (b.comap radixRegisters).mem :=
    fun i => by
      change b.mem (1 + i.val) = (input.map Signed.encode)[i.val]
      rw [hbm, ham, Nat.add_comm]
      simp [x, Data.init_mem_succ, List.getD, List.getElem?_eq_getElem i.isLt]
  obtain ⟨q, rs, heq, hqout, hqkeys, hqcounts, hnodup, horder, hset, hcounts, hframe⟩ :=
    RadixSort.deduplicate_exec (input.map Signed.encode) (b.comap radixRegisters)
      (by simpa only [List.length_map] using hb_len) hb_src
      (by rw [hb_dst, List.length_map]; omega) hb_bits hmem
      (by
        intro u hu
        obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hu
        exact key_lt_two_pow hU (hvalues z hz))
      (input_fits input hw hvalues).2 (by simpa only [List.length_map] using hN) hB h2
  have hrlen : rs.length ≤ n := by
    have ht := hnodup.length_le_of_subset (fun k hk => (hset k).mp hk)
    simpa only [List.length_map] using ht
  let c := q.extend radixRegisters b
  have hradix := heq.rename radixRegisters_injective
  have hhigh (i : Fin 24) : c.regs (parameterRegisters i) = a.regs (parameterRegisters i) := by
    rw [Data.extend_regs_of_forall_ne _ _ _ (fun j he => by
      have := congrArg Fin.val he; dsimp only [radixRegisters, parameterRegisters] at this; omega)]
    exact hb_high i
  have hcn := (hhigh _).trans han
  have hcU := (hhigh _).trans haU
  have hcB := (hhigh _).trans haB
  have hrawkeys : ∀ v ∈ rs, v.1 ≤ 2 * U + 1 ∧ v.1 / 2 ≤ U := by
    intro v hv
    obtain ⟨z, hz, he⟩ := List.mem_map.mp ((hset v.1).mp (List.mem_map.mpr ⟨v, hv, rfl⟩))
    rw [← he]
    exact ⟨(Math.key_bounds (hvalues z hz)).1, by
      rw [Signed.encode_div_two]
      exact_mod_cast (show (z.natAbs : ℤ) ≤ (U : ℤ) by
        simpa only [Int.natCast_natAbs] using hvalues z hz)⟩
  obtain ⟨y, htail, hor, hy_base, hy_count, hy_end, hrkeys, hrcounts, hrframe⟩ :
      ∃ y, ExecWithin w (.seq arraySetup (.seq (Arrays.program.rename arrayRegisters) finish))
          c y (9 + (l.arrays * (43 * rs.length + 32) + 21 + 3)) ∧
        Output l U rs y.mem ∧
        y.regs descriptorBase = l.descriptors ∧
        y.regs descriptorCount = l.count ∧
        y.regs heapEnd = l.endpoint ∧
        Block.HoldsList (1 + 2 * n) (rs.map Prod.fst) y.mem ∧
        Block.HoldsList (1 + 3 * n) (rs.map Prod.snd) y.mem ∧
        Modifies (Block.mk l.descriptors (l.endpoint - l.descriptors)).footprint c.mem y.mem := by
    refine WP.exists_execWithin ?_
    unfold arraySetup finish
    wram_exec [c, hcn, hcU, hcB, hqout]
    wram_call (Arrays.exec l rs _
      (by wram_simp) (by wram_simp [l, layout]) (by wram_simp)
      (by wram_simp [l, layout]; omega) (by wram_simp [l, layout]; omega)
      (by wram_simp) (by wram_simp [Layout.descriptors, l, layout]; omega)
      hrlen (by wram_simp [c, l, layout, n]; simpa only [List.length_map] using hqkeys)
      (by wram_simp [c, l, layout, n]; simpa only [List.length_map] using hqcounts)
      hrawkeys hfront)
      canonical arrayRegisters_injective with e ⟨hor, hregs, _, hrkeys, hrcounts, hrframe⟩
    wram_exec [hregs.descriptors, hregs.triples, hregs.heapEnd]
    wram_simp
    exact ⟨hor, hrkeys, hrcounts, hrframe⟩
  have hconstruct : ExecWithin w construct a y
      (4 + (RadixSort.deduplicateTime n l.digits +
        (9 + (l.arrays * (43 * rs.length + 32) + 21 + 3)))) := by
    simpa only [construct, List.length_map, hb_bits, n] using hb.seq (hradix.seq htail)
  have hall := ha.seq hconstruct
  refine ⟨y, rs, ?_, hor, hy_base, hy_count, hy_end, hnodup, horder, hset, hcounts,
    hrkeys, hrcounts, ?_, ?_⟩
  · apply hall.mono
    simpa only [cost, List.length_map, n, U, l, layout] using cost_sum_bound
      (ChanHe.Parameters.time κ n U) (RadixSort.deduplicateTime n l.digits)
      l.arrays n rs.length hrlen
  · have hprf (i : Fin 24) : y.regs (parameterRegisters i) = a.regs (parameterRegisters i) :=
      hconstruct.regs_eq (construct_preserves_parameters i)
    -- Only register equalities are needed: the parameter output does not constrain memory.
    exact ⟨(hprf _).trans hop.len, (hprf _).trans hop.magnitude,
      (hprf _).trans hop.digits, (hprf _).trans hop.height, (hprf _).trans hop.fuel,
      (hprf _).trans hop.want, (hprf _).trans hop.primeBound,
      (hprf _).trans hop.packedLen, (hprf _).trans hop.padding⟩
  · intro baddr hbaddr
    have hnot (s k : ℕ) (hs : 1 ≤ s) (he : s + k ≤ l.endpoint) :
        baddr ∉ (Block.mk s k).footprint := fun hba => hbaddr (by
      change baddr ∈ (Block.mk 1 (l.endpoint - 1)).footprint
      rw [Block.mem_footprint] at hba ⊢
      dsimp only [Block.Owns] at hba ⊢
      omega)
    have hdesc : 1 ≤ l.descriptors := by dsimp only [Layout.descriptors]; omega
    have hde : l.descriptors ≤ l.endpoint := by
      dsimp only [Layout.endpoint, Layout.pointer, Layout.payloads, Layout.descriptors, l, layout]
      omega
    have hbe : 1 + 4 * n ≤ l.endpoint := by
      dsimp only [Layout.endpoint, Layout.pointer, Layout.payloads, Layout.descriptors, l, layout]
      omega
    rw [hrframe baddr (hnot _ _ hdesc (by omega)), Data.extend_mem,
      hframe baddr (by simpa only [List.length_map, n] using hnot 1 (4 * n) le_rfl hbe),
      Data.comap_mem, hbm, ham]

end Cslib.Algorithms.WordRAM.ThreeSum.Frontend
