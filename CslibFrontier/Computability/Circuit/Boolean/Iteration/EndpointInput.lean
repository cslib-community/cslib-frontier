/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Iteration.EndpointPower
public import CslibFrontier.Computability.Circuit.Boolean.Iteration.InputTime
import CslibFrontier.Computability.Circuit.Boolean.Iteration.Decoder
import CslibFrontier.Computability.Circuit.Boolean.Iteration.CheckpointCycle
import CslibFrontier.Computability.Circuit.Boolean.Iteration.EndpointOptimization
import CslibFrontier.Computability.Circuit.Boolean.Iteration.LiveShort
import CslibFrontier.Computability.Circuit.Boolean.Iteration.TransientWindow
import CslibFrontier.Computability.Circuit.Boolean.Word

/-!
# Powers of a Boolean circuit with a binary input exponent

`input_time_endpoint` builds one circuit for all times encoded by the `m` exponent bits.
For a size-`s` transition on `n` bits and `N = 2^n` states, its size is
`O(min(N, √(N (s + (n+1)²))) + n*m)`. This size-dependent bound is an original result of this
development. The circuit is nonuniform in the transition.

`input_time_endpoint_tradeoff` gives the bound for each window length. The least-rank scan
returns a checkpoint and the distance already walked. For a transient target, an ancestry
and depth lookup implements Reitwiessner's transient selection rule [Reitwiessner2026InputTime].
It selects a checkpoint within a short walk of the answer. For a cyclic target,
streaming remainder computes the target phase and a lookup selects the start of its cycle block.
-/

public section

namespace Cslib.Circuits.Boolean.Iteration

open FunctionalGraph

variable {n m L : ℕ}

private theorem exists_endpointPrefix (c q : Circuit signature n n) (hL : 0 < L) :
    ∃ (out : Circuit signature n (n + n)) (delay : BitString n → ℕ),
      out.Computes interpretation (fun x => Fin.append ((c.eval interpretation)^[delay x] x)
        (fun j : Fin n => (BitVec.ofNat n (delay x)).getLsbD j.val)) ∧
      (∀ x, delay x < L ∧
        (Function.Injective (fun j : Fin (2 * L) => (c.eval interpretation)^[j.val] x) →
          IsEndpointCheckpoint (c.eval interpretation) (fun z => toLex (q.eval interpretation z))
            L ((c.eval interpretation)^[delay x] x))) ∧
      out.size ≤ 2 * L * (c.size + q.size + 24 * n + 2) + 2 := by
  let K := 2 * L
  let f := c.eval interpretation
  let first : Fin K := ⟨0, by dsimp [K]; lia⟩
  let cut (i : Fin K) := if i.val < L then i.val else i.val - L
  have hcut (i : Fin K) : cut i < L := by
    have := i.isLt
    dsimp [cut, K] at *
    split <;> lia
  let states (x : BitString n) (i : Fin K) := f^[i.val] x
  let ranks (x : BitString n) (i : Fin K) := q.eval interpretation (states x i)
  let flags (x : BitString n) := leastRankFlag (ranks x) first
  let index (x : BitString n) := chooseRecord (flags x) id first K
  let row (x : BitString n) (i : Fin K) := Fin.append (f^[cut i] x)
    (fun j : Fin n => (BitVec.ofNat n (cut i)).getLsbD j.val)
  have ht : Synthesis interpretation (inputs n) (prefixWires f K) (K * c.size) :=
    Synthesis.orbit (s := inputs n) c id (fun j => ⟨j, rfl⟩) K
  let s := inputs n ∪ prefixWires f K
  have hf := synthesis_leastRankFlag s q states first fun i j =>
    Or.inr (prefix_mem f i.isLt.le j)
  let s' := s ∪ Set.range fun j x => flags x j
  have hconst := (Synthesis.const (s := s') false).union (Synthesis.const (s := s') true)
  let src := s' ∪ ({fun _ => false} ∪ {fun _ => true} : Set (BooleanFunction n))
  have hbit (b : Bool) : (fun _ : BitString n => b) ∈ src := by cases b <;> simp [src]
  have hrow (i : Fin K) (j : Fin (n + n)) : (fun x => row x i j) ∈ src := by
    cases j using Fin.addCases with
    | left j =>
      simpa only [row, Fin.append_left] using
        (show (fun x => f^[cut i] x j) ∈ src from
          Or.inl (Or.inl (Or.inr (prefix_mem f (by have := hcut i; dsimp [K]; lia) j))))
    | right j => simpa only [row, Fin.append_right] using hbit _
  have hr := synthesis_chooseRecord src flags row (fun x => row x first)
    (fun j => Or.inl (Or.inr ⟨j, rfl⟩)) hrow (hrow first)
  obtain ⟨out, hout, hs⟩ := (ht.trans (hf.trans (hconst.trans hr))).exists_circuit_outputs
  refine ⟨out, fun x => cut (index x), fun x => ?_, fun x => ⟨hcut _, fun hi => ?_⟩,
    hs.trans (le_of_eq (by dsimp only [K]; ring))⟩
  · rw [hout x]
    change chooseRecord (flags x) (row x) (row x first) K = row x (index x)
    exact (chooseRecord_map (row x) (flags x) id first K).symm
  · obtain ⟨⟨j, hj⟩, hmin⟩ := leastRankFlag_spec (ranks x) first
    obtain ⟨i, _, hflag, he⟩ := chooseRecord_spec (flags x) id first K ⟨j, j.isLt, hj⟩
    dsimp only [index, id] at he ⊢
    exact he ▸ isEndpointCheckpoint_of_min f _ hi i (hmin i hflag)

/-- Feed the selected checkpoint and the unspent time to a circuit that answers queries
starting at a mark. Both operands of the subtraction are widened, so the time may have any
number of bits. -/
private theorem exists_shiftedQuery (c q : Circuit signature n n) (hL : 0 < L) (hLN : L ≤ 2 ^ n)
    (query : Circuit signature (n + (n + m)) n)
    (hq : ∀ h, IsEndpointCheckpoint (c.eval interpretation)
        (fun z => toLex (q.eval interpretation z)) L h → ∀ u : BitVec (n + m),
      query.eval interpretation (Fin.append h (BitString.equivBitVec.symm u)) =
        (c.eval interpretation)^[u.toNat] h) :
    ∃ out : Circuit signature (n + m) n,
      (∀ x (t : BitVec m), 2 * L ≤ t.toNat →
        Function.Injective (fun j : Fin (2 * L) => (c.eval interpretation)^[j.val] x) →
        out.eval interpretation (Fin.append x (BitString.equivBitVec.symm t)) =
          (c.eval interpretation)^[t.toNat] x) ∧
      out.size ≤ 2 * L * (c.size + q.size + 24 * n + 2) + query.size + 13 * (n + m) + 4 := by
  obtain ⟨scan, delay, hp, hd, hsize⟩ := exists_endpointPrefix c q hL
  let start (y : BitString (n + m)) : BitString n := fun j => y (Fin.castAdd m j)
  let time (y : BitString (n + m)) := BitString.equivBitVec fun j : Fin m => y (Fin.natAdd n j)
  let raw y := scan.eval interpretation (start y)
  let mark y : BitString n := fun j => raw y (Fin.castAdd n j)
  let offset y := BitString.equivBitVec fun j : Fin n => raw y (Fin.natAdd n j)
  let remTime y := (time y).setWidth (n + m) - (offset y).setWidth (n + m)
  have hpref : Synthesis interpretation (inputs (n + m)) (wires raw) scan.size :=
    Synthesis.circuit scan (fun j y => start y j) (fun j => ⟨_, rfl⟩)
  let s := inputs (n + m) ∪ wires raw
  let src := s ∪ {fun _ => false}
  have hz : (fun _ : BitString (n + m) => false) ∈ src := Or.inr rfl
  have ht : wordWires time ⊆ src := by
    rintro _ ⟨j, rfl⟩
    simpa only [time, BitString.getLsbD_equivBitVec] using
      (show (fun y : BitString (n + m) => y (Fin.natAdd n j)) ∈ src from Or.inl (Or.inl ⟨_, rfl⟩))
  have hdw : wordWires offset ⊆ src := by
    rintro _ ⟨j, rfl⟩
    simpa only [offset, BitString.getLsbD_equivBitVec] using
      (show (fun y => raw y (Fin.natAdd n j)) ∈ src from Or.inl (Or.inr ⟨_, rfl⟩))
  have hr := Synthesis.word_sub (s := src) (fun y => (time y).setWidth (n + m))
    (fun y => (offset y).setWidth (n + m))
    (fun j => wordWires_setWidth_subset ht hz ⟨j, rfl⟩)
    (fun j => wordWires_setWidth_subset hdw hz ⟨j, rfl⟩)
  let arg y := Fin.append (mark y) (BitString.equivBitVec.symm (remTime y))
  have hc := Synthesis.circuit (I := interpretation) (s := src ∪ wordWires remTime) query
    (fun i y => arg y i) fun i => by
      cases i using Fin.addCases with
      | left j => simpa only [arg, Fin.append_left] using
          (show (fun y => mark y j) ∈ src ∪ wordWires remTime from
            Or.inl (Or.inl (Or.inr ⟨_, rfl⟩)))
      | right j => simpa only [arg, Fin.append_right, BitString.equivBitVec_symm_apply,
          ← BitVec.getLsbD_eq_getElem] using
          (show (fun y => (remTime y).getLsbD j.val) ∈ src ∪ wordWires remTime from Or.inr ⟨j, rfl⟩)
  obtain ⟨out, ho, hs⟩ :=
    (hpref.trans ((Synthesis.const false).trans (hr.trans hc))).exists_circuit_outputs
  refine ⟨out, fun x t ht0 hinj => ?_, by lia⟩
  let y := Fin.append x (BitString.equivBitVec.symm t)
  have hx : start y = x := funext fun j => by simp [start, y]
  have htime : time y = t := by simp only [time, y, Fin.append_right, Equiv.apply_symm_apply]
  have hraw : raw y = Fin.append ((c.eval interpretation)^[delay x] x)
      (fun j : Fin n => (BitVec.ofNat n (delay x)).getLsbD j.val) :=
    (congrArg (scan.eval interpretation) hx).trans (hp x)
  have hmark : mark y = (c.eval interpretation)^[delay x] x := funext fun j => by
    simp only [mark, hraw, Fin.append_left]
  have hoff : offset y = BitVec.ofNat n (delay x) := by
    simp only [offset, hraw, Fin.append_right, BitString.equivBitVec_getLsbD]
  have hdLt := (hd x).1
  have hsub : (remTime y).toNat = t.toNat - delay x := by
    have htw : (t.setWidth (n + m)).toNat = t.toNat := BitVec.toNat_setWidth_of_le (by lia)
    have hdw' : ((BitVec.ofNat n (delay x)).setWidth (n + m)).toNat = delay x := by
      rw [BitVec.toNat_setWidth_of_le (by lia), BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (hdLt.trans_le hLN)]
    dsimp only [remTime]
    rw [htime, hoff, BitVec.toNat_sub_of_le (by rw [BitVec.le_def, htw, hdw']; omega), htw, hdw']
  refine (ho y).trans ?_
  change query.eval interpretation
    (Fin.append (mark y) (BitString.equivBitVec.symm (remTime y))) = _
  rw [hmark, hq _ ((hd x).2 hinj), hsub, ← Function.iterate_add_apply,
    Nat.sub_add_cancel (by omega)]

/-- Select the state returned by a flagged branch or the value of the fallback circuit. -/
private theorem exists_branch {a b : ℕ} (branch : Circuit signature a b)
    (fallback : Circuit signature a n) (flag : Fin b) (state : Fin n → Fin b) :
    ∃ out : Circuit signature a n, out.Computes interpretation (fun x =>
      if branch.eval interpretation x flag then fun j => branch.eval interpretation x (state j)
      else fallback.eval interpretation x) ∧ out.size ≤ branch.size + fallback.size + 4 * n := by
  let s := (inputs a ∪ wires (branch.eval interpretation)) ∪ wires (fallback.eval interpretation)
  have hb := Synthesis.circuit (s := inputs a) (I := interpretation) branch (fun i x => x i)
    (fun i => ⟨i, rfl⟩)
  have hf := Synthesis.circuit (s := inputs a) (I := interpretation) fallback (fun i x => x i)
    (fun i => ⟨i, rfl⟩)
  have hm := synthesis_bits_mux s (fun x j => branch.eval interpretation x (state j))
    (fallback.eval interpretation) (fun x => branch.eval interpretation x flag)
    (by rintro _ ⟨j, rfl⟩; exact Or.inl (Or.inr ⟨_, rfl⟩)) (fun _ h => Or.inr h)
    (Or.inl (Or.inr ⟨_, rfl⟩))
  have hs := hb.trans ((hf.mono Set.subset_union_left Set.Subset.rfl le_rfl).trans hm)
  obtain ⟨out, ho, hsize⟩ := hs.exists_circuit_outputs
  exact ⟨out, ho, by lia⟩

/-- A single input-time query from a checkpoint can end either in its transient tree or on
its eventual cycle. The transient circuit also supplies the branch bit. -/
private theorem exists_markedPower {w : ℕ} (c q : Circuit signature n n)
    (H : Finset (BitString n)) (hL : 0 < L) (hLN : L ≤ 2 ^ n)
    (hH : ∀ x, x ∈ H ↔ IsEndpointCheckpoint (c.eval interpretation)
      (fun z => toLex (q.eval interpretation z)) L x) :
    ∃ out : Circuit signature (n + w) n, (∀ h ∈ H, ∀ u : BitVec w,
      out.eval interpretation (Fin.append h (BitString.equivBitVec.symm u)) =
        (c.eval interpretation)^[u.toNat] h) ∧
      out.size ≤ 2200 * (H.card + 2 ^ n / L + 2 ^ ((n + 1) / 2) +
        L * (c.size + (n + 1) ^ 2) + (n + 1) * (w + 1)) := by
  let f := c.eval interpretation
  let rank z := toLex (q.eval interpretation z)
  obtain ⟨tree, hflag, htree, htreeSize⟩ := transient_window_circuit c H (2 * L) w (by
    intro h _ u hfar ht
    obtain ⟨a, ha, hanc, hlo, hhi⟩ := exists_endpointCheckpoint_near_transient f rank
      hL h hfar.le ht.le
    exact ⟨a, (hH a).mpr ha, hanc, by simpa only [transientDepth_iterate] using hlo,
      by simpa only [transientDepth_iterate] using hhi⟩)
  obtain ⟨cycle, hcycle, hcycleSize⟩ := exists_checkpointCyclePower c H w L hL hLN
  obtain ⟨out, hval, hs⟩ := exists_branch tree cycle 0 Fin.succ
  refine ⟨out, fun h hh u => ?_, ?_⟩
  · rw [hval]
    simp only [hflag h hh, Equiv.apply_symm_apply]
    by_cases hu : u.toNat < transientDepth (c.eval interpretation) h
    · simpa only [hu, decide_true, ite_true, Equiv.apply_symm_apply, Fin.tail_def] using
        (htree h hh (BitString.equivBitVec.symm u) (by simpa using hu))
    · simpa only [hu, decide_false, Bool.false_eq_true, ite_false] using
        hcycle h hh u (Nat.le_of_not_gt hu)
  · have hc := Nat.mul_le_mul_right (n * n) hL
    have hd := Nat.mul_le_mul_right n hL
    ring_nf at htreeSize hcycleSize hs hc hd ⊢
    lia

/-- The input exponent adds a streaming arithmetic term to the same window-length tradeoff
as fixed powering. The circuit reads the state first, then the little-endian time bits. -/
theorem input_time_endpoint_tradeoff (c : Circuit signature n n) (m L : ℕ)
    (hL : 0 < L) (hLN : L ≤ 2 ^ n) :
    ∃ out : Circuit signature (n + m) n,
      out.Computes interpretation (inputTimeIterate (c.eval interpretation) m) ∧
      out.size ≤ 2000000 * (L * (c.size + (n + 1) ^ 2) + 2 ^ n / L +
        2 ^ ((n + 1) / 2) + (n + 1) * (m + 1)) := by
  rcases eq_or_ne n 0 with rfl | hn
  · exact ⟨Circuit.wiring signature Fin.elim0, fun _ => funext fun i => i.elim0,
      by rw [Circuit.size_wiring]; exact Nat.zero_le _⟩
  let f := c.eval interpretation
  obtain ⟨q, H, hq, hsize, hH⟩ := exists_endpointRank hn f hL hLN
  obtain ⟨query, hquery, querySize⟩ := exists_markedPower (w := n + m) c q H hL hLN hH
  obtain ⟨long, hlong, longSize⟩ := exists_shiftedQuery c q hL hLN query (fun h hcp =>
    hquery h ((hH h).mpr hcp))
  obtain ⟨short, hshort, shortSize⟩ := live_short_circuit c m (2 * L) (by lia)
    (Nat.mul_le_mul_left 2 hLN)
  obtain ⟨out, hout, outSize⟩ := exists_branch short long (Fin.castAdd n 0) (Fin.natAdd 1)
  refine ⟨out, fun y => ?_, ?_⟩
  · let x : BitString n := fun i => y (Fin.castAdd m i)
    let bits : BitString m := fun j => y (Fin.natAdd n j)
    let t := BitString.equivBitVec bits
    have hs := hshort y
    change (short.eval interpretation y (Fin.castAdd n 0) = true ↔
      LiveShortReady f (2 * L) x t.toNat) ∧ _ at hs
    rw [hout y]
    dsimp only
    by_cases ready : LiveShortReady f (2 * L) x t.toNat
    · rw [ite_eq_left (hs.1.mpr ready)]
      exact hs.2 ready
    · rw [ite_eq_right (fun he => ready (hs.1.mp he))]
      simpa only [inputTimeIterate, t, x, bits, Equiv.symm_apply_apply,
        Fin.append_castAdd_natAdd] using
        hlong x t (Nat.le_of_not_gt (fun ht => ready (.inl ht)))
          (injective_of_not_liveShortReady ready)
  · have hcard : H.card ≤ 512 * (2 ^ n / L + 1) := Nat.le_of_lt <|
      Nat.lt_of_mul_lt_mul_right (a := L) (by nlinarith [Nat.lt_mul_div_succ (2 ^ n) hL])
    have hRank := Nat.mul_le_mul_left L hq
    have hSquare := Nat.mul_le_mul_right (n * n) hL
    have hLinear := Nat.mul_le_mul_right n hL
    have hHalf : 1 ≤ 2 ^ ((n + 1) / 2) := Nat.one_le_two_pow
    ring_nf at querySize longSize shortSize outSize hcard hRank hSquare hLinear ⊢
    lia

/-- An `m`-bit input exponent costs an additive `n*m` term on top of the optimized fixed-power
bound. The circuit is nonuniform in the transition and computes every representable time. -/
theorem input_time_endpoint (c : Circuit signature n n) (m : ℕ) :
    ∃ out : Circuit signature (n + m) n,
      out.Computes interpretation (inputTimeIterate (c.eval interpretation) m) ∧
      (out.size : ℝ) ≤ 64000000 *
        (min ((2 : ℝ) ^ n) (Real.sqrt ((2 : ℝ) ^ n * (c.size + (n + 1) ^ 2 : ℕ))) + n * m) := by
  convert exists_inputTime_of_endpoint_tradeoff c m 2000000
    (fun g L => input_time_endpoint_tradeoff g m L) using 4
  norm_num

end Cslib.Circuits.Boolean.Iteration
