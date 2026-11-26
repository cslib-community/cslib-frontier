/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.Progress
public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.Return

/-!
# Accumulation after a proved native child return

## Main results

* `PrunedQuery.exec_progress_return`: actual indexed signed accumulation establishes the next
  partial sum, using the child's ordinary value and frame postconditions.

Execution of the child is composed separately by the depth induction. This lemma proves the
parent's subsequent native instructions; no child execution or cost certificate is input here.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery

open Cslib.WordRAM Cslib.WordRAM.Signed
open Cslib.Algorithms.MatrixMultiplication.Schonhage

private theorem notMem_childWrites_frame {L f d j : ℕ} (hd : d < L) (hj : j < 4) :
    f + 4 * d + j ∉ childWrites L f d := by
  simp only [childWrites, Finset.mem_union, Block.mem_footprint, Block.Owns]
  omega

private theorem notMem_childWrites_values {L f d q : ℕ} (hd : d < L)
    (hq : q < 10 ^ L) :
    f + 4 * (L + 1) + (L + 1) * 10 ^ L + d * 10 ^ L + q ∉ childWrites L f d := by
  simp only [childWrites, Finset.mem_union, Block.mem_footprint, Block.Owns]
  have hm := Nat.mul_le_mul_right (10 ^ L) (by omega : d + 2 ≤ L + 1)
  simp only [Nat.add_mul, Nat.two_mul, Nat.one_mul] at hm ⊢
  omega

/-- Ordinary child postconditions suffice to prove the actual parent accumulation step.
All signed fits follow from the common original-input magnitude envelope. -/
theorem exec_progress_return {w L f a0 b0 n d p E A B : ℕ}
    (S : Finset (OutStr (n + 1))) (a b : Leaf (n + 1) → ℤ)
    (x y u z : Data registers) (hx : NodeReady L f a0 b0 (n + 1) d p E S x) (k : Fin 10)
    (hy : NodeProgress L f a0 b0 n d p E S a b x k.val y)
    (hne : (childSet S (Encoding.termDigits k)).Nonempty)
    (hpush : Modifies (childWrites L f d) y.mem u.mem)
    (hz : NodeResult L f a0 b0 n (d + 1) (y.regs epoch + 1)
      (childSet S (Encoding.termDigits k))
      (sliceAt a (Encoding.termDigits k)) (sliceAt b (Encoding.termDigits k)) u z)
    (ha : ∀ v, |a v| ≤ (A : ℤ)) (hb : ∀ v, |b v| ≤ (B : ℤ))
    (hw : 0 < w) (hmag : magnitudeBound L A B < 2 ^ (w - 1))
    (hfit : Fits (w + 2) (nodeBudget L f a0 b0 E (n + 1))) :
    ∃ v, ExecWithin (w + 2) step z v (31 * S.card + 29) ∧
      NodeProgress L f a0 b0 n d p E S a b x (k.val + 1) v := by
  obtain ⟨hd, hdn, hn⟩ : d < L ∧ d + 1 ≤ L ∧ n + 1 ≤ L := by have := hx.depth_add; omega
  have hpow := Nat.pow_le_pow_right (by decide : 1 ≤ (10 : ℕ)) hn
  have henv := magnitudeBound_fits hw hmag
  have hsub := childWrites_subset_nodeWrites (f := f) hd
  have hsub' := nodeWrites_child_subset (f := f) hd
  have hmid : Modifies (nodeWrites L f d) y.mem z.mem := by
    intro c hc
    exact (hz.frame c (fun h => hc (hsub' h))).trans (hpush c (fun h => hc (hsub h)))
  have hparent (j : ℕ) (hj : j < 4) : z.mem (f + 4 * d + j) = y.mem (f + 4 * d + j) :=
    (hz.frame _ (notMem_nodeWrites_ancestor_frame hdn (by omega) hj)).trans
      (hpush _ (notMem_childWrites_frame hd hj))
  have hvalues (q : ℕ) (hq : q < 10 ^ L) :
      z.mem (f + 4 * (L + 1) + (L + 1) * 10 ^ L + d * 10 ^ L + q) =
        y.mem (f + 4 * (L + 1) + (L + 1) * 10 ^ L + d * 10 ^ L + q) :=
    (hz.frame _ (notMem_nodeWrites_ancestor_values hdn (by omega) hq)).trans
      (hpush _ (notMem_childWrites_values hd hq))
  let input := fun i => x.mem (f + 4 * (L + 1) + d * 10 ^ L + i)
  have hinput : ∀ i < S.card, z.mem (f + 4 * (L + 1) + d * 10 ^ L + i) = input i := fun i hi =>
    (hmid _ (notMem_nodeWrites_list hd.le (hi.trans_le hx.card_le))).trans (hy.requests i hi)
  have hquery : ∀ i < S.card, ∃ q ∈ S, (queryIndex q).val = input i :=
    fun i hi => hx.exists_of_read hi
  have hcodes : ∀ i < S.card, input i < 10 ^ L := fun i hi => (hx.read_lt hi).trans_le hpow
  let V := fun c => if h : c < 10 ^ (n + 1) then
    partialValue a b S (queryAt ⟨c, h⟩) k.val else 0
  let C := fun c => if h : c < 10 ^ n then
    Pruned.childResult a b S (Encoding.termDigits k) (queryAt ⟨c, h⟩) else 0
  have hV (q : OutStr (n + 1)) : V (queryIndex q).val = partialValue a b S q k.val := by
    simp only [V, dite_eq_left (queryIndex q).isLt, Fin.eta, queryAt_queryIndex]
  have hC (q : OutStr n) : C (queryIndex q).val =
      Pruned.childResult a b S (Encoding.termDigits k) q := by
    simp only [C, dite_eq_left (queryIndex q).isLt, Fin.eta, queryAt_queryIndex]
  have hsel (q : OutStr (n + 1)) : selected true k.val (queryIndex q).val ↔
      (Encoding.termDigits k).Contributes (q 0) := by
    simp only [selected, ↓reduceIte, queryIndex_mod, contributes_iff_digit]
  have hlevel : z.regs level = d := by
    simpa only [ite_eq_right (by omega : d + 1 ≠ 0), Nat.add_sub_cancel_right] using hz.level_eq
  have hactive : z.regs active = 1 := by
    simpa only [ite_eq_right (by omega : d + 1 ≠ 0)] using hz.active_eq
  have hN : z.mem (f + 4 * d) = S.card := (hparent 0 (by decide)).trans (hy.frame 0)
  have hterm : z.mem (f + 4 * d + 3) = k.val := (hparent 3 (by decide)).trans (hy.frame 3)
  have hparentValues : ∀ i < S.card,
      z.mem (f + 4 * (L + 1) + (L + 1) * 10 ^ L + d * 10 ^ L + input i) =
        encode (V (input i)) := fun i hi => by
    obtain ⟨q, hq, he⟩ := hquery i hi
    rw [← he, hvalues _ ((queryIndex q).isLt.trans_le hpow), hy.values q hq, hV]
  have hchildValues : ∀ i < S.card, selected true k.val (input i) →
      z.mem (f + 4 * (L + 1) + (L + 1) * 10 ^ L + (d + 1) * 10 ^ L + input i / 10) =
        encode (C (input i / 10)) := fun i hi hselected => by
    obtain ⟨q, hq, he⟩ := hquery i hi
    have htail : Fin.tail q ∈ childSet S (Encoding.termDigits k) :=
      mem_childSet.mpr ⟨q, hq, (hsel q).mp (he ▸ hselected), rfl⟩
    rw [← he, queryIndex_div, hC]
    simpa only [Pruned.childResult, hne, ↓reduceIte] using hz.values (Fin.tail q) htail
  obtain ⟨v, hv, hregs, hlevel', hmode, hactive', hepoch, hresult, hfirst, hterm',
      hstamp, hframe⟩ := exec_node_return (N := S.card) (k := k.val) z hz.regs hlevel hd
    (hz.mode_eq (by omega)) hN hx.card_le hterm k.isLt input V C hinput hcodes hx.injOn_read
    hparentValues hchildValues
    (fun i hi => by
      obtain ⟨q, _, he⟩ := hquery i hi; rw [← he, hV]
      exact fits_partialValue hn henv a b ha hb S q k.val)
    (fun i hi => by
      obtain ⟨q, _, he⟩ := hquery i hi; rw [← he, queryIndex_div, hC]
      exact fits_childResult (by omega) henv a b ha hb S _ _)
    (hfit.of_le (by unfold nodeBudget; omega))
  refine ⟨v, hv, ⟨hregs, hlevel', hmode, hactive'.trans hactive, ?_,
    fun i hi => (hframe _ (notMem_nodeWrites_list hd.le (hi.trans_le hx.card_le))).trans
      (hinput i hi),
    ?_, hepoch ▸ hy.epoch_le.trans ((Nat.le_succ _).trans hz.epoch_le),
    by rw [hepoch, Nat.add_mul, Nat.one_mul]; have := hz.epoch_upper; have := hy.epoch_upper; omega,
    fun q hq => by rw [hstamp q hq, hepoch]; exact hz.timestamps q hq, ?_⟩⟩
  · intro j
    fin_cases j
    · exact (hfirst 0 (by decide)).trans hN
    · exact ((hfirst 1 (by decide)).trans (hparent 1 (by decide))).trans (hy.frame 1)
    · exact ((hfirst 2 (by decide)).trans (hparent 2 (by decide))).trans (hy.frame 2)
    · exact hterm'
  · intro q hq
    obtain ⟨i, hi, (he : input i = (queryIndex q).val)⟩ := hx.exists_read hq
    have hr := hresult i hi
    rw [he, hV, queryIndex_div, hC] at hr
    simpa only [partialValue_succ, hsel] using hr
  · simpa only [Finset.union_self] using (hy.footprint.trans hmid).trans hframe

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery
