/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Iteration.InputTime
public import CslibFrontier.Computability.Circuit.Boolean.Iteration.Label
import CslibFrontier.Computability.Circuit.Boolean.Iteration.Remainder
import CslibFrontier.Computability.Circuit.Boolean.Iteration.Ranked
import CslibFrontier.Foundations.Data.BitString.BitVec
import CslibFrontier.Tactic.Synthesis
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Input-time queries with a short prefix or a short return

After computing the first `2 * K` steps once, a circuit handles every input time below
`K` and every orbit for which the state at `K` returns in at most `K` more steps. It
reduces a long input time modulo the detected period and selects the corresponding
state from the same prefix. A separate output bit reports when this suffices.
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Iteration

open Function FunctionalGraph

variable {a n m w K : ℕ}

/-- The prefix answers this input-time query directly or contains a full return from time `K`. -/
def LiveShortReady (f : BitString n → BitString n) (K : ℕ) (x : BitString n) (t : ℕ) : Prop :=
  t < K ∨ ∃ j : Fin K, f^[j.val + 1] (f^[K] x) = f^[K] x

/-- If the short-query branch is unavailable, the orbit has a simple prefix of length `K`. -/
theorem injective_of_not_liveShortReady {f : BitString n → BitString n} {x : BitString n}
    {t : ℕ} (h : ¬ LiveShortReady f K x t) :
    Function.Injective (fun j : Fin K => f^[j.val] x) :=
  injective_of_no_return_period f x (fun e => h (.inr e))

private theorem shortLength_of_return (f : BitString n → BitString n) (z : BitString n)
    (hKw : K < 2 ^ w) (hr : ∃ j : Fin K, f^[j.val + 1] z = z) :
    let p := (shortLength (w := w) f K z).toNat
    0 < p ∧ p ≤ K ∧ f^[p] z = z := by
  obtain ⟨j, hj⟩ := hr
  have hp := mk_mem_periodicPts (Nat.succ_pos j.val) (show IsPeriodicPt f _ z from hj)
  have hm := cycleLength_eq_minimalPeriod_of_mem_periodicPts f hp
  have hK : cycleLength f z ≤ K := by
    rw [hm]
    exact (IsPeriodicPt.minimalPeriod_le (Nat.succ_pos j.val) hj).trans j.isLt
  simp only [shortLength_eq f K hp hK, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hK.trans_lt hKw)]
  exact ⟨cycleLength_pos f z, hK, hm ▸ isPeriodicPt_minimalPeriod f z⟩

private theorem shortLength_of_no_return (f : BitString n → BitString n) (z : BitString n)
    (hr : ¬ ∃ j : Fin K, f^[j.val + 1] z = z) : shortLength (w := w) f K z = 0 := by
  have hz (i : Fin (K + 1)) : decide (0 < i.rev.val ∧ f^[i.rev.val] z = z) = false := by
    apply decide_eq_false
    rintro ⟨hp, he⟩
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
    refine hr ⟨⟨j, by have := i.rev.isLt; lia⟩, ?_⟩
    change f^[j + 1] z = z
    simpa only [hj, Nat.succ_eq_add_one] using he
  unfold shortLength firstIndex chooseFirst
  rw [chooseRecord_of_forall_eq_false _ _ _ hz]
  have he : (fun _ : Fin w => false) = (fun i : Fin w => (0 : BitVec w).getLsbD i.val) :=
    funext fun _ => BitVec.getLsbD_zero.symm
  rw [he, BitString.equivBitVec_getLsbD]

private theorem synthesis_time_lt (s : Set (BooleanFunction a)) (bits : BitString a → BitString m)
    (hb : wires bits ⊆ s) (hc : ∀ b : Bool, (fun _ : BitString a => b) ∈ s) (K : ℕ) :
    Synthesis interpretation s {fun x => decide ((BitString.equivBitVec (bits x)).toNat < K)}
      (5 * m + 2) := by
  by_cases hk : K < 2 ^ m
  · have h := Synthesis.word_ult (s := s) (fun x => BitString.equivBitVec (bits x))
      (fun _ => BitVec.ofNat m K)
      (fun i => by simpa only [BitString.getLsbD_equivBitVec] using hb ⟨i, rfl⟩) (fun _ => hc _)
    simpa only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk] using h
  · have h (x : BitString a) : (BitString.equivBitVec (bits x)).toNat < K :=
      (BitString.equivBitVec (bits x)).isLt.trans_le (le_of_not_gt hk)
    simpa only [h, decide_true] using
      (Synthesis.of_mem (I := interpretation) (hc true)).mono
        Set.Subset.rfl Set.Subset.rfl (Nat.zero_le (5 * m + 2))

private theorem liveShortReady_iff (f : BitString n → BitString n) (x : BitString n) (t : ℕ)
    (hKw : K < 2 ^ w) :
    (decide (t < K) || !decide (shortLength (w := w) f K (f^[K] x) = 0)) = true ↔
      LiveShortReady f K x t := by
  simp only [LiveShortReady, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq,
    decide_eq_false_iff_not]
  by_cases hr : ∃ j : Fin K, f^[j.val + 1] (f^[K] x) = f^[K] x
  · have hp := (shortLength_of_return f _ hKw hr).1
    have hn : shortLength (w := w) f K (f^[K] x) ≠ 0 := by
      intro h
      rw [h] at hp
      exact (Nat.lt_irrefl 0) hp
    exact ⟨fun _ => Or.inr hr, fun _ => Or.inr hn⟩
  · rw [shortLength_of_no_return f _ hr]
    simp only [not_true_eq_false, or_false, hr]

private theorem liveShortValue (f : BitString n → BitString n) (x : BitString n)
    (bits : BitString m) (hK : 0 < K) (hw : 2 * K ≤ 2 ^ w)
    (hready : LiveShortReady f K x (BitString.equivBitVec bits).toNat) :
    let d := shortLength (w := w) f K (f^[K] x)
    let index := periodicTimeIndex K d bits (decide ((BitString.equivBitVec bits).toNat < K))
    selectBits index (fun j : Fin (2 * K) => f^[j.val] x) =
      f^[(BitString.equivBitVec bits).toNat] x := by
  let t := (BitString.equivBitVec bits).toNat
  let d := shortLength (w := w) f K (f^[K] x)
  let index := periodicTimeIndex K d bits (decide ((BitString.equivBitVec bits).toNat < K))
  have hKw : K < 2 ^ w := by lia
  change selectBits index _ = f^[t] x
  by_cases ht : t < K
  · have he : index.toNat = t := by
      simp only [index, periodicTimeIndex, show (BitString.equivBitVec bits).toNat < K from ht,
        decide_true, ↓reduceIte, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (ht.trans hKw), t]
    rw [selectBits_of_toNat_lt _ _ (by rw [he]; lia)]
    exact congrArg (fun j => f^[j] x) he
  · obtain ⟨hp, hpK, hret⟩ := shortLength_of_return f _ hKw (hready.resolve_left ht)
    have he : index.toNat = K + (t - K) % d.toNat := by
      change (periodicTimeIndex K d bits (decide (t < K))).toNat = _
      rw [decide_eq_false ht]
      exact toNat_periodicTimeIndex_long K d bits (le_of_not_gt ht) hp (by lia) (by lia)
    rw [selectBits_of_toNat_lt _ _ (by rw [he]; have := Nat.mod_lt (t - K) hp; lia)]
    change f^[index.toNat] x = f^[t] x
    rw [he, Nat.add_comm K, iterate_add_apply]
    have hperiod : IsPeriodicPt f d.toNat (f^[K] x) := hret
    rw [hperiod.iterate_mod_apply, ← iterate_add_apply, Nat.sub_add_cancel (le_of_not_gt ht)]

/-- A joint circuit returns a ready bit followed by `n` state bits. Whenever the time is below
`K` or the orbit returns from its `K`-th state within `K` steps, the state bits give the input-time
iterate. The scan advances the circuit exactly `2 * K` times, and the cost of reading the
`m`-bit input time is additive. -/
theorem live_short_circuit (c : Circuit signature n n) (m K : ℕ) (hK : 0 < K)
    (hKn : K ≤ 2 * 2 ^ n) :
    ∃ out : Circuit signature (n + m) (1 + n),
      (∀ y : BitString (n + m),
        let x := fun i : Fin n => y (Fin.castAdd m i)
        let t := (BitString.equivBitVec (fun j : Fin m => y (Fin.natAdd n j))).toNat
        ((out.eval interpretation y (Fin.castAdd n 0) = true) ↔
          LiveShortReady (c.eval interpretation) K x t) ∧
        (LiveShortReady (c.eval interpretation) K x t →
          (fun i => out.eval interpretation y (Fin.natAdd 1 i)) =
            inputTimeIterate (c.eval interpretation) m y)) ∧
      out.size ≤ 2 * K * c.size + 1200 * (K + 1) * (n + 1) ^ 2 + 100 * (m + 1) * (n + 1) := by
  let w := n + 2
  let f := c.eval interpretation
  let x := fun y : BitString (n + m) => fun i : Fin n => y (Fin.castAdd m i)
  let bits := fun y : BitString (n + m) => fun i : Fin m => y (Fin.natAdd n i)
  let t := fun y => (BitString.equivBitVec (bits y)).toNat
  let last := fun y => f^[K] (x y)
  let period := fun y => shortLength (w := w) f K (last y)
  let short := fun y => decide (t y < K)
  let ready := fun y => short y || !decide (period y = 0)
  let index := fun y => periodicTimeIndex K (period y) (bits y) (short y)
  let rows := fun (j : Fin (2 * K)) y => f^[j.val] (x y)
  let answer := fun y => selectBits (index y) (fun j => rows j y)
  let packed := fun y => Fin.append (fun _ : Fin 1 => ready y) (answer y)
  let src : Set (BooleanFunction (n + m)) := inputs (n + m)
  have hx (i : Fin n) : (fun y => x y i) ∈ src := ⟨Fin.castAdd m i, rfl⟩
  have hb : wires bits ⊆ src := fun _ ⟨i, h⟩ => h ▸ ⟨Fin.natAdd n i, rfl⟩
  let b := Synthesis.Builder.start interpretation src
  let b := b.add (Synthesis.const false)
  let b := b.add (Synthesis.const true)
  have hc (v : Bool) : (fun _ : BitString (n + m) => v) ∈ b.wires := by
    cases v <;> synthesis_available
  let trace := Synthesis.stages (fun j => wires fun y => f^[j] (x y)) (2 * K)
  have htrace : Synthesis interpretation b.wires trace (2 * K * c.size) :=
    Synthesis.orbit c x (fun i => by synthesis_available) (2 * K)
  let b := b.add htrace
  have hs (j : ℕ) (hj : j ≤ 2 * K) (i : Fin n) : (fun y => f^[j] (x y) i) ∈ b.wires :=
    Or.inr (Synthesis.subset_stages _ hj ⟨i, rfl⟩)
  have hlast (j : Fin (K + 1)) (i : Fin n) : (fun y => f^[j.val] (last y) i) ∈ b.wires := by
    simpa only [last, ← iterate_add_apply] using hs (j.val + K) (by have := j.isLt; lia) i
  let b := b.add (synthesis_shortLength (w := w) b.wires f last K hlast
    (fun q => by synthesis_available))
  let b := b.add (synthesis_time_lt b.wires bits (by synthesis_available)
    (fun q => by synthesis_available) K)
  let b := b.add (Synthesis.word_eq_const period (fun i => by synthesis_available) 0)
  let b := b.add ((Synthesis.of_mem (I := interpretation) (s := b.wires)
    (show (fun y => decide (period y = 0)) ∈ b.wires by synthesis_available)).not)
  let b := b.add ((Synthesis.of_mem (I := interpretation) (s := b.wires)
    (show short ∈ b.wires by synthesis_available)).or
    (Synthesis.of_mem (show (fun y => !decide (period y = 0)) ∈ b.wires by synthesis_available)))
  let b := b.add (synthesis_periodicTimeIndex b.wires K period bits short (by synthesis_available)
    (fun i => by synthesis_available) (fun v => by synthesis_available) (by synthesis_available))
  let b := b.add (Synthesis.selectBits index rows (fun i => by synthesis_available)
    (fun j i => by
      have h := hs j.val j.isLt.le i
      synthesis_available))
  have hpack : wires packed ⊆ b.wires := by
    rintro _ ⟨i, rfl⟩
    induction i using Fin.addCases with
    | left i => simp only [packed, Fin.append_left]; synthesis_available
    | right i => simp only [packed, Fin.append_right]; synthesis_available
  have hw : 2 * K ≤ 2 ^ w := by dsimp [w]; rw [pow_add]; norm_num; lia
  have hKw : K < 2 ^ w := by lia
  obtain ⟨out, he, hsize⟩ := (b.finish hpack (k := 2 * K * c.size +
    1200 * (K + 1) * (n + 1) ^ 2 + 100 * (m + 1) * (n + 1)) (by
      dsimp +zetaDelta [Synthesis.Builder.start, Synthesis.Builder.add]
      ring_nf
      lia)).exists_circuit_outputs
  refine ⟨out, fun y => ?_, hsize⟩
  simp only [he y, packed, Fin.append_left, Fin.append_right]
  exact ⟨liveShortReady_iff (w := w) f (x y) (t y) hKw,
    fun hr => liveShortValue f (x y) (bits y) hK hw hr⟩

end Cslib.Circuits.Boolean.Iteration
