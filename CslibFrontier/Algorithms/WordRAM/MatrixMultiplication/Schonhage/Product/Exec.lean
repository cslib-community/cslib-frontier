/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Product.Cost
public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Product.MatrixInput
public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Product.Directory
public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Product.Reconstruct

/-!
# Complete actual native queried matrix products

## Main results

* `QueriedProduct.exec`: original matrix/coordinate words suffice for actual finite native
  execution, exact original-order product values, original-input restoration and outside frame.

The program computes all tables, groups, catalogues, tile arguments, epochs and reporting
decisions. The original-word predicate permits arbitrary header zero and arbitrary outside
memory; initialized clients discharge it directly from the literal `input` list.
-/

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.QueriedProduct

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Actual composed execution from only ordinary original words, with every phase charged.
No table/layout/query/producer/run/time certificate or fast-solver assumption is an input. -/
public theorem exec {w L m N A : ℕ} (hw : 0 < w) (hm : m ≤ L) (bits : Bool)
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin N) ℤ)
    (qs : List (Fin N × Fin N)) (x : Data 160)
    (hinput : ∀ a, 0 < a → a < inputEnd m N qs.length → x.mem a =
      (State.init (input bits L X Y qs) : State 160).data.mem a)
    (hX : ∀ i k, |X i k| ≤ (A : ℤ)) (hY : ∀ k j, |Y k j| ≤ (A : ℤ))
    (hbits : bits = true → (∀ i k, 0 ≤ X i k) ∧ (∀ k j, 0 ≤ Y k j))
    (hmag : magnitudeBound L A < 2 ^ (w - 1))
    (hfit : Fits (w + 2) (wordBudget L m N qs.length)) :
    ∃ y, ExecWithin (w + 2) (program bits) x y (timeBound hm qs) ∧
      Parameters L m N qs.length y ∧
      (∀ i : Fin qs.length, y.mem (outputBase L m N qs.length + i.val) =
        Signed.encode ((X * Y) (qs.get i).1 (qs.get i).2)) ∧
      (∀ a, ¬(inputEnd m N qs.length ≤ a ∧ a < memoryEnd L m N qs.length) →
        y.mem a = x.mem a) := by
  have h10 := Nat.zero_le (10 ^ L)
  have hI : 5 + 2 * (N * D m) + 2 * qs.length = inputEnd m N qs.length := rfl
  have hS := producers_le_snapshot L m N qs.length
  have hOff : snapshotBase L m N qs.length + inputEnd m N qs.length =
      offsetBase L m N qs.length := rfl
  have hCode : offsetBase L m N qs.length + numBands L m N ^ 2 + 1 =
      codeBase L m N qs.length := rfl
  have hOrig : codeBase L m N qs.length + qs.length = originalBase L m N qs.length := rfl
  have hGroup : originalBase L m N qs.length + qs.length = groupedBase L m N qs.length := rfl
  have hOut : groupedBase L m N qs.length + qs.length = outputBase L m N qs.length := rfl
  have hFree : outputBase L m N qs.length + qs.length = scratchBase L m N qs.length := rfl
  have hStamp : scratchBase L m N qs.length + 4 * (L + 1) + 2 * (L + 1) * 10 ^ L =
      stampBase L m N qs.length := rfl
  have hEnd : stampBase L m N qs.length + 10 ^ L = memoryEnd L m N qs.length := rfl
  obtain ⟨hL, hm', hN, hQ⟩ : x.mem 1 = L ∧ x.mem 2 = m ∧ x.mem 3 = N ∧ x.mem 4 = qs.length := by
    refine ⟨(hinput 1 ?_ ?_).trans ?_, (hinput 2 ?_ ?_).trans ?_, (hinput 3 ?_ ?_).trans ?_,
      (hinput 4 ?_ ?_).trans ?_⟩ <;> first | omega | simp [State.init, Data.init, input]
  have hqueries (i : ℕ) (hi : i < qs.length) :
      x.mem (queryInputBase m N + 2 * i) = (Wanted.inputPairs qs i).1 ∧
        x.mem (queryInputBase m N + 2 * i + 1) = (Wanted.inputPairs qs i).2 := by
    have hr := input_query_word bits L X Y qs ⟨i, hi⟩ 0
    have hc := input_query_word bits L X Y qs ⟨i, hi⟩ 1
    rw [hinput _ (by unfold queryInputBase; omega) (by
        simpa only [Nat.add_zero] using query_address_lt hi (by decide : 0 < 2)),
      hinput _ (by unfold queryInputBase; omega) (query_address_lt hi (by decide : 1 < 2)),
      Wanted.inputPairs_get qs ⟨i, hi⟩]
    simpa only [Fin.val_zero, Fin.val_one, Nat.add_zero, ↓reduceIte, Fin.reduceEq] using ⟨hr, hc⟩
  obtain ⟨r, old, hr, rp, rg, rv, ro, rs, rf⟩ :=
    exec_prepareRouting hm qs x hL hm' hN hQ hqueries hfit
  have rsource (j : ℕ) (hj : j < 2 * (N * D m)) :
      r.mem (snapshotBase L m N qs.length + 5 + j) =
        (State.init (input bits L X Y qs) : State 160).data.mem (5 + j) := by
    rw [show snapshotBase L m N qs.length + 5 + j =
      snapshotBase L m N qs.length + (5 + j) by omega, rs _ (by omega)]
    exact hinput _ (by omega) (by omega)
  obtain ⟨c, hc, cp, cm, cf⟩ :=
    exec_prepareInputMatrices hw bits X Y qs r rp rsource hX hY hbits hmag hfit
  obtain ⟨b, hb, bp, bl, br, bf⟩ := exec_bands hw hm X Y c cp
    ((cf 1 (Or.inl (by omega))).trans ((rf 1 (Or.inl (by omega))).trans hL))
    ((cf 2 (Or.inl (by omega))).trans ((rf 2 (Or.inl (by omega))).trans hm'))
    ((cf 3 (Or.inl (by omega))).trans ((rf 3 (Or.inl (by omega))).trans hN))
    cm hX hY hmag hfit
  obtain ⟨d, hd, dp, de, di, dm, df⟩ := exec_initializeDirectory b bp hfit
  have dg : SavedGroups L m N qs.length old d.mem :=
    rg.reframe fun a _ _ =>
      (df a (Or.inl (by omega))).trans ((bf a (Or.inr (by omega))).trans (cf a (Or.inr (by omega))))
  have de' : EncodedBands hm X Y d.mem :=
    EncodedBands.reframe ⟨bl, br⟩ fun a _ => df a (Or.inl (by omega))
  obtain ⟨t, ht, tp, tg, _, tv, tf⟩ := exec_evaluateTiles hw hm X Y qs old d dp di de
    dg de' (fun i => (rv i).1) ro dm hX hY hmag hfit
  obtain ⟨o, ho, op, ov, of⟩ := exec_reconstruct X Y qs old t tp tg (fun i => (rv i).2) tv hfit
  obtain ⟨y, hy, yp, ym⟩ := exec_restoreInput o op hfit
  refine ⟨y, (hr.seq (hc.seq (hb.seq (hd.seq (ht.seq (ho.seq hy)))))).mono
    (by unfold timeBound; omega), yp, ?_, ?_⟩
  · intro i
    rw [ym, ArrayCopy.copyPrefix_outside (by omega), ov i]
  · intro a ha
    by_cases hi : a < inputEnd m N qs.length
    · rw [ym]
      have hread := ArrayCopy.copyPrefix_read (mem := o.mem)
        (src := snapshotBase L m N qs.length) (dst := 0) hi
      have hos : o.mem (snapshotBase L m N qs.length + a) = x.mem a := by
        rw [of _ (Or.inl (by omega)), tf _ (by omega) (by omega), df _ (Or.inl (by omega)),
          bf _ (Or.inr (by omega)), cf _ (Or.inr (by omega))]
        exact rs a hi
      simpa only [Nat.zero_add] using hread.trans hos
    · have habove : memoryEnd L m N qs.length ≤ a := by omega
      rw [ym, ArrayCopy.copyPrefix_outside (by omega), of _ (Or.inr (by omega)),
        tf _ (by omega) (by omega), df _ (Or.inr habove), bf _ (Or.inr (by omega)),
        cf _ (Or.inr (by omega)), rf _ (Or.inr (by omega))]

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.QueriedProduct
