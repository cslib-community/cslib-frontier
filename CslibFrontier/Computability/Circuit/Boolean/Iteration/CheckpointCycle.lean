/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Boolean.Iteration.Label
public import CslibFrontier.Foundations.Data.BitString.BitVec
import CslibFrontier.Computability.Circuit.Boolean.Iteration.ResidueAdd
import CslibFrontier.Computability.Circuit.Boolean.Iteration.SparseLookup
import CslibFrontier.Computability.Circuit.Boolean.Word.Rewire
import CslibFrontier.Foundations.Combinatorics.FunctionalGraph.CycleBlocks

/-!
# Cyclic targets from hardwired checkpoints

Every cycle reached from a listed checkpoint is sampled at a fixed power-of-two spacing. The
canonical representative and the high bits of the target phase identify the sample. A short
orbit walk follows the low bits of the phase.

## Main results

* `Cslib.Circuits.Boolean.Iteration.exists_checkpointCyclePower` computes the cyclic target of
  a checkpoint given a binary time beyond its transient. Its gate bound charges separately
  for reading the time, the sparse cycle table, and the final walk.
-/

public section

namespace Cslib.Circuits.Boolean.Iteration

open FunctionalGraph Function

attribute [local instance] lexOrder

variable {a n : ℕ}

private theorem exists_markerPayload (f : BitString n → BitString n)
    (rows : Finset (BitString n × ℕ)) (hrows : ∀ row ∈ rows, row.2 < 2 ^ n)
    (B : ℕ) (s : Set (BooleanFunction a)) (rep : BitString a → BitString n)
    (address : BitString a → BitVec n) (hr : wires rep ⊆ s) (ha : wordWires address ⊆ s) :
    ∃ value : BitString a → BitString n,
      Synthesis interpretation s (wires value) (5 * rows.card + 24 * 2 ^ ((n + 1) / 2)) ∧
      ∀ x z j, (z, j) ∈ rows → rep x = z → (address x).toNat = j →
        value x = f^[j * B] z := by
  classical
  let e := Fintype.equivFin ↥rows
  let row (i : Fin (Fintype.card ↥rows)) := (e.symm i).val
  let repKey (i : Fin (Fintype.card ↥rows)) := (row i).1
  let blockKey (i : Fin (Fintype.card ↥rows)) :=
    BitString.equivBitVec.symm (BitVec.ofNat n (row i).2)
  let marked (i : Fin (Fintype.card ↥rows)) : BooleanFunction a :=
    fun x => decide (repKey i = rep x) &&
      decide (blockKey i = BitString.equivBitVec.symm (address x))
  let stored (i : Fin (Fintype.card ↥rows)) := f^[(row i).2 * B] (row i).1
  let value (x : BitString a) (bit : Fin n) :=
    decide (∃ i, marked i x = true ∧ stored i bit = true)
  have hr' := synthesis_tableMatches s rep hr repKey
  have hb' := synthesis_tableMatches s (fun x => BitString.equivBitVec.symm (address x)) ha blockKey
  let src := s ∪ (Set.range (fun j x => decide (repKey j = rep x)) ∪
    Set.range (fun j x => decide (blockKey j = BitString.equivBitVec.symm (address x))))
  have hm : Synthesis interpretation src (Set.range marked) (Fintype.card ↥rows) := by
    simpa using Synthesis.family (I := interpretation) (s := src) marked (fun _ => 1) fun j =>
      (Synthesis.of_mem (Or.inr (Or.inl ⟨j, rfl⟩))).and
        (Synthesis.of_mem (Or.inr (Or.inr ⟨j, rfl⟩)))
  have hv := synthesis_tablePayload (src ∪ Set.range marked) marked (fun j => Or.inr ⟨j, rfl⟩)
    stored
  refine ⟨value, ((hr'.union hb').trans (hm.trans hv)).mono
    Set.Subset.rfl Set.Subset.rfl ?_, ?_⟩
  · simp only [Fintype.card_coe]; omega
  · intro x z j hrow hrep haddr
    have match_iff (i) : marked i x = true ↔ row i = (z, j) := by
      have hbit : blockKey i = BitString.equivBitVec.symm (address x) ↔ (row i).2 = j := by
        rw [BitString.equivBitVec.symm.apply_eq_iff_eq, ← BitVec.toNat_inj, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (hrows _ (e.symm i).property), haddr]
      simp only [marked, Bool.and_eq_true, decide_eq_true_eq, hbit, hrep, repKey, Prod.ext_iff]
    funext bit
    have hi : row (e ⟨(z, j), hrow⟩) = (z, j) := congrArg Subtype.val (e.symm_apply_apply _)
    refine Bool.eq_iff_iff.mpr ?_
    simp only [value, decide_eq_true_eq, match_iff]
    exact ⟨fun ⟨i, hi, hb⟩ => by simpa [stored, hi] using hb,
      fun hb => ⟨_, hi, by simpa [stored, hi] using hb⟩⟩

/-- Select a cycle marker by its representative and the high bits of the phase, then advance
by the value of the low `b` bits. -/
private theorem exists_cycleBlockQuery (c : Circuit signature n n)
    (H : Finset (BitString n)) (b : ℕ) (s : Set (BooleanFunction a))
    (rep : BitString a → BitString n) (target : BitString a → BitVec (n + 3))
    (hr : wires rep ⊆ s) (ht : wordWires target ⊆ s) (hz : (fun _ => false) ∈ s) :
    ∃ value : BitString a → BitString n,
      Synthesis interpretation s (wires value)
        (5 * (H.card + 2 ^ n / 2 ^ b) + 24 * 2 ^ ((n + 1) / 2) +
          2 ^ b * c.size + n * (2 ^ b * (2 * b + 3) + 1)) ∧
      ∀ x, ∀ h ∈ H, rep x = canonicalCycle (c.eval interpretation) h →
        (target x).toNat < cycleLength (c.eval interpretation) h →
        value x = (c.eval interpretation)^[(target x).toNat] (rep x) := by
  classical
  let f := c.eval interpretation
  obtain ⟨rows, hcount, hbound, hcover⟩ := exists_cycleBlocks f H (2 ^ b) (Nat.two_pow_pos _)
  simp only [BitString.card] at hcount hbound
  let address := fun x => (target x >>> b).setWidth n
  let low := fun x => (target x).setWidth b
  have ha : wordWires address ⊆ s :=
    wordWires_setWidth_subset (wordWires_ushiftRight_subset ht hz) hz
  have hlo : wordWires low ⊆ s := wordWires_setWidth_subset ht hz
  obtain ⟨start, hs, hstart⟩ := exists_markerPayload f rows hbound (2 ^ b) s rep address hr ha
  let src := s ∪ wires start
  let trace := Synthesis.stages (fun j => wires fun x => f^[j] (start x)) (2 ^ b)
  have ho : Synthesis interpretation src trace (2 ^ b * c.size) :=
    Synthesis.orbit c start (fun i => Or.inr ⟨i, rfl⟩) (2 ^ b)
  have hsel := Synthesis.selectBits (s := src ∪ trace) low
    (fun j : Fin (2 ^ b) => fun x => f^[j.val] (start x))
    (fun i => Or.inl (Or.inl (hlo ⟨i, rfl⟩)))
    fun j i => Or.inr (Synthesis.subset_stages _ j.isLt.le ⟨i, rfl⟩)
  refine ⟨fun x => selectBits (low x) (fun j : Fin (2 ^ b) => f^[j.val] (start x)),
    (hs.trans (ho.trans hsel)).mono Set.Subset.rfl Set.Subset.rfl (by lia), ?_⟩
  intro x h hh hrep hp
  let p := (target x).toNat
  have hfit : p / 2 ^ b < 2 ^ n :=
    (Nat.div_le_self _ _).trans_lt (hp.trans_le (cycleLength_le_two_pow f h))
  have ha' : (address x).toNat = p / 2 ^ b := by
    simp only [address, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
      Nat.shiftRight_eq_div_pow, p, Nat.mod_eq_of_lt hfit]
  have hlo' : (low x).toNat = p % 2 ^ b := BitVec.toNat_setWidth _ _
  simp only [selectBits_of_toNat_lt _ _ (low x).isLt,
    hstart x (canonicalCycle f h) (p / 2 ^ b) (hcover h hh p hp) hrep ha', ← hrep,
    ← iterate_add_apply, hlo', Nat.mul_comm (p / 2 ^ b), Nat.mod_add_div, f, p]

private theorem cycleQueryBudget_le (n w D g L : ℕ) (hL : 0 < L) (hLN : L ≤ 2 ^ n) :
    let b := Nat.log 2 L
    let h := 2 ^ ((n + 1) / 2)
    let h' := 2 ^ ((n + 3 + 1) / 2)
    (3 * D + 8 * h + 8 * h) + (3 * D + 8 * h + 8 * h') + (3 * D + 8 * h + 8 * h') + 1 +
      (w * (22 * (n + 3) + 3) + (100 * (n + 3 + 1) +
        (5 * (D + 2 ^ n / 2 ^ b) + 24 * h + 2 ^ b * g + n * (2 ^ b * (2 * b + 3) + 1)))) ≤
      2000 * (D + 2 ^ n / L + h + L * (g + (n + 1) ^ 2) + (n + 1) * (w + 1)) := by
  intro b h h'
  have hB : 2 ^ b ≤ L := Nat.pow_log_le_self _ hL.ne'
  have hbn : b ≤ n := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (hB.trans hLN)
  have hBL : L ≤ 2 * 2 ^ b := by
    simpa only [b, pow_succ, Nat.mul_comm] using (Nat.lt_pow_succ_log_self (by decide : 1 < 2) L).le
  have hhalf : h' ≤ 4 * h := calc
    _ ≤ 2 ^ ((n + 1) / 2 + 2) := Nat.pow_le_pow_right (by decide) (by lia)
    _ = _ := by rw [pow_add]; ring
  have htable : 2 ^ n / 2 ^ b < 2 * (2 ^ n / L + 1) := by
    apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr
    calc
      _ < L * (2 ^ n / L + 1) := Nat.lt_mul_div_succ _ hL
      _ ≤ (2 * 2 ^ b) * (2 ^ n / L + 1) := Nat.mul_le_mul_right _ hBL
      _ = _ := by ring
  have hsel : n * (2 ^ b * (2 * b + 3) + 1) ≤ n * (L * (2 * n + 3) + 1) := by gcongr
  have hstep := Nat.mul_le_mul_right g hB
  grw [hhalf, htable.le, hsel, hstep]
  ring_nf
  lia

/-- A live exponent at a named checkpoint, once its trajectory is cyclic. Input coordinates
are the checkpoint followed by `w` low-bit-first time bits. Reading its canonical cycle label,
a streaming remainder, one sampled cycle marker, and the short final walk are all charged. -/
theorem exists_checkpointCyclePower {n : ℕ} (c : Circuit signature n n)
    (H : Finset (BitString n)) (w L : ℕ) (hL : 0 < L) (hLN : L ≤ 2 ^ n) :
    ∃ d : Circuit signature (n + w) n,
      (∀ h ∈ H, ∀ u : BitVec w, transientDepth (c.eval interpretation) h ≤ u.toNat →
        d.eval interpretation (Fin.append h (BitString.equivBitVec.symm u)) =
          (c.eval interpretation)^[u.toNat] h) ∧
      d.size ≤ 2000 * (H.card + 2 ^ n / L + 2 ^ ((n + 1) / 2) +
        L * (c.size + (n + 1) ^ 2) + (n + 1) * (w + 1)) := by
  classical
  let f := c.eval interpretation
  let key (x : BitString (n + w)) := x ∘ Fin.castAdd w
  let time (x : BitString (n + w)) := x ∘ Fin.natAdd n
  let s₀ := inputs (n + w) (U := Bool)
  have hk : wires key ⊆ s₀ := by rintro _ ⟨i, rfl⟩; exact ⟨Fin.castAdd w i, rfl⟩
  obtain ⟨rep, hr, hr_spec⟩ := exists_synthesis_sparseLookup H (canonicalCycle f) s₀ key hk
  obtain ⟨phaseBits, hp, hp_spec⟩ := exists_synthesis_sparseLookup H
    (fun y => BitString.equivBitVec.symm (BitVec.ofNat (n + 3) (phase f y))) s₀ key hk
  obtain ⟨lengthBits, hl, hl_spec⟩ := exists_synthesis_sparseLookup H
    (fun y => BitString.equivBitVec.symm (BitVec.ofNat (n + 3) (cycleLength f y))) s₀ key hk
  let phi := fun x => BitString.equivBitVec (phaseBits x)
  let ell := fun x => BitString.equivBitVec (lengthBits x)
  let s₁ := s₀ ∪ ((wires rep ∪ wires phaseBits ∪ wires lengthBits) ∪ {fun _ => false})
  have hmeta := (((hr.union hp).union hl).union (Synthesis.const (s := s₀) false))
  have hword (field : BitString (n + w) → BitString (n + 3)) (hf : wires field ⊆ s₁) :
      wordWires (fun x => BitString.equivBitVec (field x)) ⊆ s₁ := by
    rintro _ ⟨i, rfl⟩
    simpa only [BitString.getLsbD_equivBitVec] using hf ⟨i, rfl⟩
  have hphi : wordWires phi ⊆ s₁ :=
    hword phaseBits fun _ hi => Or.inr (Or.inl (Or.inl (Or.inr hi)))
  have hell : wordWires ell ⊆ s₁ := hword lengthBits fun _ hi => Or.inr (Or.inl (Or.inr hi))
  have hrep : wires rep ⊆ s₁ := fun _ hi => Or.inr (Or.inl (Or.inl (Or.inl hi)))
  have hz : (fun _ => false) ∈ s₁ := Or.inr (Or.inr rfl)
  let rem := fun x => streamRemainder (ell x) (time x)
  let s₂ := s₁ ∪ wordWires rem
  have hrem := synthesis_streamRemainder s₁ ell time (fun i => hell ⟨i, rfl⟩)
    (fun i => Or.inl ⟨Fin.natAdd n i, rfl⟩) hz
  let target := fun x => addResidue (ell x) (phi x) (rem x)
  let s₃ := s₂ ∪ wordWires target
  have hadd := synthesis_addResidue s₂ ell phi rem
    (hell.trans Set.subset_union_left) (hphi.trans Set.subset_union_left) Set.subset_union_right
  obtain ⟨out, hout, hout_spec⟩ := exists_cycleBlockQuery c H (Nat.log 2 L) s₃ rep target
    ((hrep.trans Set.subset_union_left).trans Set.subset_union_left) Set.subset_union_right
    (Or.inl (Or.inl hz))
  obtain ⟨d, hd, hs⟩ := (hmeta.trans (hrem.trans (hadd.trans hout))).exists_circuit_outputs
  refine ⟨d, ?_, hs.trans (cycleQueryBudget_le n w H.card c.size L hL hLN)⟩
  intro h hh u hcyc
  let x := Fin.append h (BitString.equivBitVec.symm u)
  have hkey : key x = h := funext fun i => Fin.append_left _ _ i
  have htime : time x = BitString.equivBitVec.symm u := funext fun i => Fin.append_right _ _ i
  have hvalid : key x ∈ H := hkey ▸ hh
  have hl' : (ell x).toNat = cycleLength f h := by
    simp only [ell, hl_spec x hvalid, hkey, Equiv.apply_symm_apply, toNat_ofNat_cycleLength]
  have hp' : (phi x).toNat = phase f h := by
    simp only [phi, hp_spec x hvalid, hkey, Equiv.apply_symm_apply, toNat_ofNat_phase]
  have hr' := (hr_spec x hvalid).trans (congrArg (canonicalCycle f) hkey)
  have hroom : 2 * (ell x).toNat ≤ 2 ^ (n + 3) := by
    have := cycleLength_le_two_pow f h
    rw [hl', pow_add]; omega
  have hrem' : (rem x).toNat = u.toNat % cycleLength f h := by
    simpa only [rem, htime, Equiv.apply_symm_apply, hl'] using
      toNat_streamRemainder (ell x) (time x) (hl' ▸ cycleLength_pos f h) hroom
  have ht : (target x).toNat = (phase f h + u.toNat) % cycleLength f h := by
    rw [toNat_addResidue _ _ _ (by simpa only [hp', hl'] using phase_lt f h)
      (by simpa only [hrem', hl'] using Nat.mod_lt u.toNat (cycleLength_pos f h)),
      hp', hrem', hl', Nat.add_mod_mod]
  exact (hd x).trans <| by
    simpa only [hout_spec x h hh hr' (ht ▸ Nat.mod_lt _ (cycleLength_pos f h)), hr', ht] using
      (iterate_eq_iterate_phase f h hcyc).symm

end Cslib.Circuits.Boolean.Iteration
