/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Computability.Circuit.Boolean.Basic
public import CslibFrontier.Foundations.Combinatorics.FunctionalGraph
public import CslibFrontier.Foundations.Data.BitString.BitVec
import CslibFrontier.Computability.Circuit.Boolean.Iteration.Scan
import CslibFrontier.Computability.Circuit.Boolean.Iteration.SparseLookup
import CslibFrontier.Foundations.Combinatorics.FunctionalGraph.EndpointCheckpoints
import CslibFrontier.Foundations.Combinatorics.FunctionalGraph.ForestIntervals
import CslibFrontier.Foundations.Data.BitString.Binary

/-!
# Transient targets from a checkpoint forest

A comparison against a hardwired full-width threshold can reuse every equality and threshold
test on the two half-words. Consequently searching a table of forest intervals costs linearly
in the number of checkpoints plus the size of these two shared decoders.

`transient_window_circuit` implements Reitwiessner's ancestry and depth test for an input exponent
[Reitwiessner2026InputTime] using shared half-word tables. It takes a marked state and an input
time, signals when the target is transient, and in that case outputs the iterate. The graph
hypothesis supplies a nearby marked ancestor before each long transient target.
-/

public section

namespace Cslib.Circuits.Boolean.Iteration

open FunctionalGraph

variable {a b k M : ℕ}

private theorem synthesis_prefixThresholds (s : Set (BooleanFunction a))
    (v : BitString a → Fin k) (hv : ∀ j, (fun x => decide (v x = j)) ∈ s)
    (hz : (fun _ : BitString a => false) ∈ s) :
    Synthesis interpretation s (Set.range fun j : Fin k => fun x => decide (v x ≤ j)) k := by
  let q (t : ℕ) : Set (BooleanFunction a) := {fun x => decide ((v x).val < t)}
  refine (Synthesis.steps (I := interpretation) (s := s) q 1 k (by simpa [q] using hz)
    fun t ht => ?_).mono Set.Subset.rfl ?_ (by simp)
  · refine ((Synthesis.of_mem (Or.inr (Synthesis.subset_stages q le_rfl rfl)) :
      Synthesis interpretation (s ∪ Synthesis.stages q t) {fun x => decide ((v x).val < t)} 0).or
      (Synthesis.of_mem (Or.inl (hv ⟨t, ht⟩)))).congr_iff fun _ => ?_
    simp only [Bool.or_eq_true, decide_eq_true_eq, Fin.ext_iff]
    lia
  · rintro _ ⟨j, rfl⟩
    exact Synthesis.subset_stages q j.isLt
      (Set.mem_singleton_iff.mpr (funext fun _ => decide_eq_decide.mpr Nat.lt_succ_iff.symm))

private def thresholdWires (v : BitString a → Fin k) : Set (BooleanFunction a) :=
  (Set.range fun j x => decide (v x ≤ j)) ∪
  (Set.range fun j x => decide (j ≤ v x)) ∪
  (Set.range fun j x => decide (v x = j))

private theorem synthesis_thresholdWires (s : Set (BooleanFunction a))
    (v : BitString a → Fin (2 ^ k)) (hv : wires (fun x => (BitString.equivFin k).symm (v x)) ⊆ s) :
    Synthesis interpretation s (thresholdWires v) (6 * 2 ^ k + 1) := by
  let eqs := Set.range fun j x => decide (v x = j)
  have he : Synthesis interpretation s eqs (4 * 2 ^ k) :=
    (synthesis_allMinterms s (fun x => (BitString.equivFin k).symm (v x)) hv).mono
      Set.Subset.rfl (by
        rintro _ ⟨j, rfl⟩
        exact ⟨(BitString.equivFin k).symm j, funext fun _ => by simp⟩) le_rfl
  let src := s ∪ ({fun _ : BitString a => false} ∪ eqs)
  have hz : (fun _ : BitString a => false) ∈ src := Or.inr (Or.inl rfl)
  have he' (j : Fin (2 ^ k)) : (fun x => decide (v x = j)) ∈ src := Or.inr (Or.inr ⟨j, rfl⟩)
  have hlo := synthesis_prefixThresholds src v he' hz
  have hhi := synthesis_prefixThresholds src (fun x => (v x).rev)
    (fun j => by simpa only [Fin.rev_eq_iff] using he' j.rev) hz
  refine (((Synthesis.const false).union he).comp (hlo.union hhi)).mono Set.Subset.rfl ?_ (by lia)
  rintro _ ((⟨j, rfl⟩ | ⟨j, rfl⟩) | ⟨j, rfl⟩)
  · exact Or.inr (Or.inl ⟨j, rfl⟩)
  · exact Or.inr (Or.inr ⟨j.rev, funext fun _ => by simp⟩)
  · exact Or.inl (Or.inr ⟨j, rfl⟩)

private def lowPart (k : ℕ) (x : Fin (2 ^ b)) : Fin (2 ^ k) :=
  ⟨x.val % 2 ^ k, Nat.mod_lt _ (Nat.two_pow_pos _)⟩

private def highPart (k : ℕ) (hk : k ≤ b) (x : Fin (2 ^ b)) : Fin (2 ^ (b - k)) :=
  ⟨x.val / 2 ^ k, by
    apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr
    rw [← pow_add, Nat.sub_add_cancel hk]
    exact x.isLt⟩

private theorem le_split (k : ℕ) (hk : k ≤ b) (x y : Fin (2 ^ b)) :
    x ≤ y ↔ highPart k hk x ≤ highPart k hk y ∧
      (highPart k hk x = highPart k hk y → lowPart k x ≤ lowPart k y) := by
  simp only [Fin.le_def, Fin.ext_iff, highPart, lowPart]
  have hx := Nat.mod_add_div x.val (2 ^ k)
  have hy := Nat.mod_add_div y.val (2 ^ k)
  refine ⟨fun h => ⟨Nat.div_le_div_right h, fun he => ?_⟩, fun ⟨h, he⟩ => ?_⟩
  · rw [he] at hx; omega
  · obtain hlt | hq := h.lt_or_eq
    · exact le_of_not_gt fun hn => hlt.not_ge (Nat.div_le_div_right hn.le)
    · rw [hq] at hx; omega

private theorem synthesis_splitTests (s : Set (BooleanFunction a)) (v : BitString a → Fin (2 ^ b))
    (hv : wires (fun x => (BitString.equivFin b).symm (v x)) ⊆ s)
    (c : Fin M → Fin (2 ^ b)) (reverse : Bool) :
    Synthesis interpretation s (Set.range fun j x => decide
      (if reverse then c j ≤ v x else v x ≤ c j))
      (6 * (2 ^ (b / 2) + 2 ^ (b - b / 2)) + 2 + 3 * M) := by
  let k := b / 2
  have hk : k ≤ b := Nat.div_le_self _ _
  let lo := fun x => lowPart k (v x)
  let hi := fun x => highPart k hk (v x)
  have hlo := synthesis_thresholdWires s lo (by
    rintro _ ⟨i, rfl⟩
    simpa only [lo, lowPart, BitString.equivFin_symm_apply, Nat.testBit_mod_two_pow,
      i.isLt, decide_true, Bool.true_and, Fin.val_castLE] using hv ⟨Fin.castLE hk i, rfl⟩)
  have hhi := synthesis_thresholdWires s hi (by
    rintro _ ⟨i, rfl⟩
    simpa only [hi, highPart, BitString.equivFin_symm_apply, Nat.testBit_div_two_pow]
      using hv ⟨⟨i.val + k, by have := i.isLt; lia⟩, rfl⟩)
  let src := s ∪ (thresholdWires lo ∪ thresholdWires hi)
  have row (j : Fin M) : Synthesis interpretation src
      {fun x => decide (if reverse then c j ≤ v x else v x ≤ c j)} 3 := by
    let C := highPart k hk (c j)
    let D := lowPart k (c j)
    let eqh := fun x => decide (hi x = C)
    let testHi := fun x => decide (if reverse then C ≤ hi x else hi x ≤ C)
    let testLo := fun x => decide (if reverse then D ≤ lo x else lo x ≤ D)
    have hEq : Synthesis interpretation src {eqh} 0 :=
      Synthesis.of_mem (Or.inr (Or.inr (Or.inr ⟨C, rfl⟩)))
    have htHi : Synthesis interpretation src {testHi} 0 := Synthesis.of_mem <| by
      cases reverse
      exacts [Or.inr (Or.inr (Or.inl (Or.inl ⟨C, rfl⟩))),
        Or.inr (Or.inr (Or.inl (Or.inr ⟨C, rfl⟩)))]
    have htLo : Synthesis interpretation src {testLo} 0 := Synthesis.of_mem <| by
      cases reverse
      exacts [Or.inr (Or.inl (Or.inl (Or.inl ⟨D, rfl⟩))),
        Or.inr (Or.inl (Or.inl (Or.inr ⟨D, rfl⟩)))]
    refine (htHi.and (hEq.not.or htLo)).congr_iff fun x => ?_
    cases reverse <;>
      simp only [testHi, testLo, eqh, le_split k hk, Bool.false_eq_true, ite_false, ite_true,
        Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
        decide_eq_true_eq] <;>
      grind
  refine ((hlo.union hhi).trans (Synthesis.family (s := src) _ _ row)).mono
    Set.Subset.rfl Set.Subset.rfl ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul, k]; omega

private def beforeFlag (flags : Fin M → Bool) (t : ℕ) : Bool :=
  decide (∃ i : Fin M, i.val < t ∧ flags i = true)

private def firstFlag (flags : Fin M → Bool) (j : Fin M) : Bool :=
  flags j && !beforeFlag flags j.val

private theorem firstFlag_spec (flags : Fin M → Bool) (h : ∃ j, flags j = true) :
    ∃ j, flags j = true ∧ ∀ i, firstFlag flags i = true ↔ i = j := by
  classical
  let hits := Finset.univ.filter fun j => flags j = true
  have hh : hits.Nonempty := by simpa [hits, Finset.Nonempty] using h
  let j := hits.min' hh
  have hj : flags j = true := (Finset.mem_filter.mp (hits.min'_mem hh)).2
  have hm {i} (hi : flags i = true) : j ≤ i :=
    hits.min'_le i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
  refine ⟨j, hj, fun i => ?_⟩
  simp only [firstFlag, beforeFlag, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
  exact ⟨fun ⟨hi, hnone⟩ => le_antisymm (le_of_not_gt fun hlt => hnone ⟨j, hlt, hj⟩) (hm hi),
    fun h => h ▸ ⟨hj, fun ⟨i, hil, hi⟩ => (hm hi).not_gt hil⟩⟩

private theorem synthesis_firstFlag (s : Set (BooleanFunction a))
    (flags : BitString a → Fin M → Bool) (hf : ∀ j, (fun x => flags x j) ∈ s) :
    Synthesis interpretation s (Set.range fun j x => firstFlag (flags x) j) (1 + 3 * M) := by
  let q (t : ℕ) : Set (BooleanFunction a) := {fun x => beforeFlag (flags x) t}
  let src := s ∪ {fun _ : BitString a => false}
  have hsteps := Synthesis.steps (I := interpretation) (s := src) q 1 M
    (Set.singleton_subset_iff.mpr (Or.inr (by simp [beforeFlag]))) fun t ht => ?_
  · let seen := src ∪ Synthesis.stages q M
    have hflags := Synthesis.family (s := seen) (fun j x => firstFlag (flags x) j) (fun _ => 2)
      fun j => (Synthesis.of_mem (Or.inl (Or.inl (hf j))) :
        Synthesis interpretation seen {fun x => flags x j} 0).and
        (Synthesis.of_mem (Or.inr (Synthesis.subset_stages q j.isLt.le rfl))).not
    apply ((Synthesis.const false).trans (hsteps.trans hflags)).mono Set.Subset.rfl Set.Subset.rfl
    simp [Nat.mul_comm]; lia
  · let i : Fin M := ⟨t, ht⟩
    refine ((Synthesis.of_mem (Or.inr (Synthesis.subset_stages q le_rfl rfl)) :
      Synthesis interpretation (src ∪ Synthesis.stages q t) {fun x => beforeFlag (flags x) t} 0).or
      (Synthesis.of_mem (Or.inl (Or.inl (hf i))))).congr_iff fun x => ?_
    simp only [beforeFlag, Bool.or_eq_true, decide_eq_true_eq, Nat.lt_succ_iff, le_iff_lt_or_eq]
    exact ⟨fun h => h.elim (fun ⟨j, hj, he⟩ => ⟨j, .inl hj, he⟩) (⟨i, .inr rfl, ·⟩),
      fun ⟨j, hj, he⟩ => hj.imp (⟨j, ·, he⟩) fun h => (Fin.ext (Eq.symm h) : i = j) ▸ he⟩

private def windowFlags (q target : Fin (2 ^ b)) (lo hi floor height : Fin M → Fin (2 ^ b))
    (j : Fin M) : Bool := decide (lo j ≤ q ∧ q ≤ hi j ∧ floor j ≤ target ∧ target ≤ height j)

private theorem synthesis_windowFlags (s : Set (BooleanFunction a))
    (v d : BitString a → Fin (2 ^ b)) (lo hi floor height : Fin M → Fin (2 ^ b))
    (hv : wires (fun x => (BitString.equivFin b).symm (v x)) ⊆ s)
    (hd : wires (fun x => (BitString.equivFin b).symm (d x)) ⊆ s) :
    Synthesis interpretation s (Set.range fun j x => windowFlags (v x) (d x) lo hi floor height j)
      (15 * M + 48 * 2 ^ ((b + 1) / 2) + 8) := by
  let rankTests := (synthesis_splitTests s v hv lo true).union
    (synthesis_splitTests s v hv hi false)
  let tests := rankTests.union
    ((synthesis_splitTests s d hd floor true).union (synthesis_splitTests s d hd height false))
  let src := s ∪ (((Set.range fun j x => decide (lo j ≤ v x)) ∪
    Set.range fun j x => decide (v x ≤ hi j)) ∪ ((Set.range fun j x => decide (floor j ≤ d x)) ∪
    Set.range fun j x => decide (d x ≤ height j)))
  have row (j : Fin M) : Synthesis interpretation src
      {fun x => windowFlags (v x) (d x) lo hi floor height j} 3 := by
    have h₁ : Synthesis interpretation src {fun x => decide (lo j ≤ v x)} 0 :=
      Synthesis.of_mem (Or.inr (Or.inl (Or.inl ⟨j, rfl⟩)))
    have h₂ : Synthesis interpretation src {fun x => decide (v x ≤ hi j)} 0 :=
      Synthesis.of_mem (Or.inr (Or.inl (Or.inr ⟨j, rfl⟩)))
    have h₃ : Synthesis interpretation src {fun x => decide (floor j ≤ d x)} 0 :=
      Synthesis.of_mem (Or.inr (Or.inr (Or.inl ⟨j, rfl⟩)))
    have h₄ : Synthesis interpretation src {fun x => decide (d x ≤ height j)} 0 :=
      Synthesis.of_mem (Or.inr (Or.inr (Or.inr ⟨j, rfl⟩)))
    exact (h₁.and (h₂.and (h₃.and h₄))).congr_iff (by simp [windowFlags])
  apply (tests.trans (Synthesis.family (s := src) _ _ row)).mono Set.Subset.rfl Set.Subset.rfl
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul]
  have h₁ := Nat.pow_le_pow_right (by decide : 0 < 2) (show b / 2 ≤ (b + 1) / 2 by lia)
  have h₂ := Nat.pow_le_pow_right (by decide : 0 < 2) (show b - b / 2 ≤ (b + 1) / 2 by lia)
  lia

private def chosenWord (flags : Fin M → Bool) (rows : Fin M → BitString b) : BitString b :=
  fun bit => decide (∃ j, firstFlag flags j = true ∧ rows j bit = true)

private theorem chosenWord_eq (flags : Fin M → Bool) (j : Fin M)
    (huniq : ∀ i, firstFlag flags i = true ↔ i = j) (rows : Fin M → BitString b) :
    chosenWord flags rows = rows j := by
  funext bit
  simp [chosenWord, huniq]

attribute [local instance] lexOrder

private noncomputable def depthCode (f : BitString b → BitString b)
    (x : BitString b) : Fin (2 ^ b) :=
  ⟨transientDepth f x, by simpa using transientDepth_lt_card f x⟩

private noncomputable def rankCode (f : BitString b → BitString b)
    (x : BitString b) : Fin (2 ^ b) :=
  ⟨(forestRank f x).val, by simpa using (forestRank f x).isLt⟩

private noncomputable def upperCode (f : BitString b → BitString b)
    (x : BitString b) : Fin (2 ^ b) :=
  ⟨(forestUpper f x).val, by simpa using (forestUpper f x).isLt⟩

private def bitCode (i : Fin (2 ^ b)) : BitString b := (BitString.equivFin b).symm i

private theorem code_toNat (i : Fin (2 ^ b)) :
    (BitString.equivBitVec (bitCode i)).toNat = i.val := by
  rw [BitString.toNat_equivBitVec_eq_equivFin, bitCode, Equiv.apply_symm_apply]

private def shortWalk (f : BitString b → BitString b) (K : ℕ) (start : BitString b)
    (height target : BitString b) : BitString b :=
  selectBits (BitString.equivBitVec height - BitString.equivBitVec target)
    fun j : Fin (K + 1) => f^[j.val] start

private theorem shortWalk_spec (f : BitString b → BitString b) (K : ℕ) (start : BitString b)
    (height target : Fin (2 ^ b)) (h : target ≤ height) (hs : height.val - target.val ≤ K) :
    shortWalk f K start (bitCode height) (bitCode target) = f^[height.val - target.val] start := by
  have hd : (BitString.equivBitVec (bitCode height) - BitString.equivBitVec (bitCode target)).toNat
      = height.val - target.val := by
    rw [BitVec.toNat_sub_of_le (by simpa only [BitVec.le_def, code_toNat] using Fin.le_def.mp h),
      code_toNat, code_toNat]
  rw [shortWalk, selectBits_of_toNat_lt _ _ (by rw [hd]; omega)]
  simp only [hd]

private theorem synthesis_shortWalk (s : Set (BooleanFunction a)) (c : Circuit signature b b)
    (K : ℕ) (start height target : BitString a → BitString b) (hx : wires start ⊆ s)
    (hh : wires height ⊆ s) (ht : wires target ⊆ s) :
    Synthesis interpretation s (wires fun x => shortWalk (c.eval interpretation) K (start x)
      (height x) (target x)) (K * c.size + (13 * b + 1) + b * ((K + 1) * (2 * b + 3) + 1)) := by
  let trace := Synthesis.stages (fun j => wires fun x => (c.eval interpretation)^[j] (start x)) K
  let steps := fun x => BitString.equivBitVec (height x) - BitString.equivBitVec (target x)
  have htrace : Synthesis interpretation s trace (K * c.size) :=
    Synthesis.orbit c start (fun i => hx ⟨i, rfl⟩) K
  have hsub := Synthesis.word_sub (s := s) (fun x => BitString.equivBitVec (height x))
    (fun x => BitString.equivBitVec (target x))
    (fun i => by simpa only [BitString.getLsbD_equivBitVec] using hh ⟨i, rfl⟩)
    (fun i => by simpa only [BitString.getLsbD_equivBitVec] using ht ⟨i, rfl⟩)
  have hsel := Synthesis.selectBits (s := s ∪ (trace ∪ wordWires steps)) steps
    (fun (j : Fin (K + 1)) x => (c.eval interpretation)^[j.val] (start x))
    (fun i => Or.inr (Or.inr ⟨i, rfl⟩))
    (fun j bit => Or.inr (Or.inl (Synthesis.subset_stages _ (Nat.le_of_lt_succ j.isLt) ⟨bit, rfl⟩)))
  exact (htrace.union hsub).trans hsel

private theorem transient_from_labels (s : Set (BooleanFunction a)) (c : Circuit signature b b)
    (K : ℕ) (marks : Fin M → BitString b) (start : BitString a → BitString b)
    (v target : BitString a → Fin (2 ^ b)) (hv : wires (fun x => bitCode (v x)) ⊆ s)
    (ht : wires (fun x => bitCode (target x)) ⊆ s) :
    ∃ output : BitString a → BitString b, (Synthesis interpretation s (wires output)
      (22 * M + 64 * 2 ^ ((b + 1) / 2) + 9 +
        (K * c.size + (13 * b + 1) + b * ((K + 1) * (2 * b + 3) + 1)))) ∧
      ∀ x t, v x = rankCode (c.eval interpretation) (start x) →
      (target x).val = transientDepth (c.eval interpretation) (start x) - t →
      t < transientDepth (c.eval interpretation) (start x) →
      (∃ i, (∃ j ≤ transientDepth (c.eval interpretation) (start x),
        (c.eval interpretation)^[j] (start x) = marks i) ∧
        (target x).val ≤ transientDepth (c.eval interpretation) (marks i) ∧
        transientDepth (c.eval interpretation) (marks i) ≤ (target x).val + K) →
      output x = (c.eval interpretation)^[t] (start x) := by
  let f := c.eval interpretation
  let lo := fun i => rankCode f (marks i)
  let hi := fun i => upperCode f (marks i)
  let dep := fun i => depthCode f (marks i)
  let floor (i : Fin M) : Fin (2 ^ b) :=
    ⟨(dep i).val - K, lt_of_le_of_lt (Nat.sub_le _ _) (dep i).isLt⟩
  let flags := fun x => windowFlags (v x) (target x) lo hi floor dep
  let base := fun x => chosenWord (flags x) marks
  let levels := fun i => bitCode (dep i)
  let depth := fun x => chosenWord (flags x) levels
  have hf := synthesis_windowFlags s v target lo hi floor dep hv ht
  let src := s ∪ Set.range fun j x => flags x j
  have hfirst := synthesis_firstFlag src flags fun j => Or.inr ⟨j, rfl⟩
  let ready := src ∪ Set.range fun j x => firstFlag (flags x) j
  have hmark (j : Fin M) : (fun x => firstFlag (flags x) j) ∈ ready := Or.inr ⟨j, rfl⟩
  have hb := synthesis_tablePayload ready _ hmark marks
  have hd := synthesis_tablePayload ready _ hmark levels
  have hw := synthesis_shortWalk (ready ∪ (wires base ∪ wires depth)) c K base depth
    (fun x => bitCode (target x)) (fun _ h => Or.inr (Or.inl h)) (fun _ h => Or.inr (Or.inr h))
    (fun _ h => Or.inl (Or.inl (Or.inl (ht h))))
  refine ⟨fun x => shortWalk f K (base x) (depth x) (bitCode (target x)),
    (hf.trans (hfirst.trans ((hb.union hd).trans hw))).mono Set.Subset.rfl Set.Subset.rfl (by lia),
    fun x t hpre htarget ht' ⟨hit, hhit⟩ => ?_⟩
  have flag_iff (i : Fin M) : flags x i = true ↔
      (∃ j ≤ transientDepth f (start x), f^[j] (start x) = marks i) ∧
      (target x).val ≤ (dep i).val ∧ (dep i).val ≤ (target x).val + K := by
    simp only [flags, windowFlags, decide_eq_true_eq, hpre]
    have hz := forest_interval_spec f (start x) (marks i)
    change ((lo i).val ≤ (rankCode f (start x)).val ∧
      (rankCode f (start x)).val ≤ (hi i).val ∧ (dep i).val - K ≤ (target x).val ∧
      (target x).val ≤ (dep i).val) ↔ _
    change ((lo i).val ≤ (rankCode f (start x)).val ∧
      (rankCode f (start x)).val ≤ (hi i).val) ↔ _ at hz
    refine ⟨fun ⟨h₁, h₂, h₃, h₄⟩ => ⟨hz.mp ⟨h₁, h₂⟩, h₄, by lia⟩, fun ⟨ha, h₁, h₂⟩ => ?_⟩
    obtain ⟨h₃, h₄⟩ := hz.mpr ha
    exact ⟨h₃, h₄, by lia, h₁⟩
  obtain ⟨i, hi, huniq⟩ := firstFlag_spec _ ⟨hit, (flag_iff hit).mpr hhit⟩
  obtain ⟨hanc, hlo, hhi⟩ := (flag_iff i).mp hi
  have hdepth : transientDepth f (f^[t] (start x)) = (target x).val :=
    (transientDepth_iterate f (start x) t).trans htarget.symm
  obtain ⟨hk, he⟩ := iterate_of_ancestor_depth_window f ht'.le hanc
    (by rwa [hdepth]) (by rwa [hdepth])
  rw [hdepth] at hk he
  change shortWalk f K (chosenWord _ _) (chosenWord _ _) _ = _
  rwa [chosenWord_eq _ i huniq, chosenWord_eq _ i huniq, shortWalk_spec _ _ _ (dep i) _ hlo hk]

private theorem bitCode_toFin (v : BitVec b) (i : Fin b) : bitCode v.toFin i = v.getLsbD i.val := by
  simp only [bitCode, BitString.equivFin_symm_apply, BitVec.getLsbD]; rfl

/-- A live transient target from a marked starting state. The first output bit decides whether
the live time precedes the cycle. In that case the remaining outputs are the target state.
Two sparse lookups recover the starting depth and forest rank. Each marked ancestor is tested
against the target-depth window using shared half-word decoders. For a short query the start
itself is eligible. Walk at most `K` steps from the first matching ancestor. -/
theorem transient_window_circuit {n : ℕ} (c : Circuit signature n n) (H : Finset (BitString n))
    (K m : ℕ) (hcover : ∀ h ∈ H, ∀ u, K < u → u < transientDepth (c.eval interpretation) h →
      ∃ y ∈ H, (∃ j ≤ transientDepth (c.eval interpretation) h, (c.eval interpretation)^[j] h = y) ∧
      transientDepth (c.eval interpretation) h - u ≤ transientDepth (c.eval interpretation) y ∧
      transientDepth (c.eval interpretation) y ≤ transientDepth (c.eval interpretation) h - u + K) :
    ∃ out : Circuit signature (n + m) (n + 1),
      (∀ h ∈ H, ∀ t : BitString m, out.eval interpretation (Fin.append h t) 0 =
        decide ((BitString.equivBitVec t).toNat < transientDepth (c.eval interpretation) h)) ∧
      (∀ h ∈ H, ∀ t : BitString m,
        (BitString.equivBitVec t).toNat < transientDepth (c.eval interpretation) h →
        Fin.tail (out.eval interpretation (Fin.append h t)) =
          (c.eval interpretation)^[(BitString.equivBitVec t).toNat] h) ∧
      out.size ≤ 28 * H.card + 96 * 2 ^ ((n + 1) / 2) + K * c.size +
        n * ((K + 1) * (2 * n + 3) + 1) + 39 * n + 5 * m + 14 := by
  classical
  let f := c.eval interpretation
  let start := fun z : BitString (n + m) => z ∘ Fin.castAdd m
  let time := fun z : BitString (n + m) => BitString.equivBitVec (z ∘ Fin.natAdd n)
  obtain ⟨pre, hpre, hpreSize⟩ := exists_sparseLookup H fun x => bitCode (rankCode f x)
  obtain ⟨dep, hdep, hdepSize⟩ := exists_sparseLookup H fun x => bitCode (depthCode f x)
  let v := fun z => BitString.equivFin n (pre.eval interpretation (start z))
  let htWord := fun z => BitString.equivBitVec (dep.eval interpretation (start z))
  let targetWord := fun z => htWord z - (time z).setWidth n
  let target := fun z => (targetWord z).toFin
  let flag := fun z => ((time z).setWidth (n + m)).ult ((htWord z).setWidth (n + m))
  let equiv := (Fintype.equivFin ↥H).trans (finCongr (Fintype.card_coe H))
  let marks := fun i => (equiv.symm i).val
  have hp := Synthesis.circuit (I := interpretation) (s := inputs (n + m)) pre
    (fun i z => start z i) (fun i => ⟨Fin.castAdd m i, rfl⟩)
  have hd := Synthesis.circuit (I := interpretation) (s := inputs (n + m)) dep
    (fun i z => start z i) (fun i => ⟨Fin.castAdd m i, rfl⟩)
  have hstart := (Synthesis.const false (s := inputs (n + m))).union (hp.union hd)
  let src := inputs (n + m) ∪ ({fun _ : BitString (n + m) => false} ∪
    (wires (fun z => pre.eval interpretation (start z)) ∪
      wires fun z => dep.eval interpretation (start z)))
  have hz : (fun _ : BitString (n + m) => false) ∈ src := Or.inr (Or.inl rfl)
  have htimes : wordWires time ⊆ src :=
    Set.range_subset_iff.mpr fun i => Or.inl ⟨Fin.natAdd n i, by simp [time]⟩
  have hheight : wordWires htWord ⊆ src :=
    Set.range_subset_iff.mpr fun i => Or.inr (Or.inr (Or.inr ⟨i, by simp [htWord]⟩))
  have hsub := Synthesis.word_sub (s := src) htWord (fun z => (time z).setWidth n)
    (fun i => hheight ⟨i, rfl⟩) (fun i => wordWires_setWidth_subset htimes hz ⟨i, rfl⟩)
  have hflag := Synthesis.word_ult (s := src)
    (fun z => (time z).setWidth (n + m)) (fun z => (htWord z).setWidth (n + m))
    (fun i => wordWires_setWidth_subset htimes hz ⟨i, rfl⟩)
    (fun i => wordWires_setWidth_subset hheight hz ⟨i, rfl⟩)
  let ready := src ∪ ({flag} ∪ wordWires targetWord)
  obtain ⟨result, hr, hresult⟩ := transient_from_labels ready c K marks start v target
    (Set.range_subset_iff.mpr fun i => Or.inl (Or.inr (Or.inr (Or.inl
      ⟨i, by simp only [v, bitCode, Equiv.symm_apply_apply]⟩))))
    (Set.range_subset_iff.mpr fun i => Or.inr (Or.inr ⟨i, by simp only [target, bitCode_toFin]⟩))
  let output : BitString (n + m) → BitString (n + 1) := fun z => Fin.cons (flag z) (result z)
  have hs : Synthesis interpretation (inputs (n + m)) (wires output)
      (28 * H.card + 96 * 2 ^ ((n + 1) / 2) + K * c.size +
        n * ((K + 1) * (2 * n + 3) + 1) + 39 * n + 5 * m + 14) := by
    refine (hstart.trans ((hflag.union hsub).comp hr)).mono Set.Subset.rfl ?_ (by lia)
    rintro _ ⟨i, rfl⟩
    exact Fin.cases (Or.inl (Or.inl rfl)) (fun i => Or.inr ⟨i, by simp [output]⟩) i
  obtain ⟨out, heval, hs⟩ := hs.exists_circuit_outputs
  have hStart (h : BitString n) (t : BitString m) : start (Fin.append h t) = h :=
    funext fun i => Fin.append_left _ _ i
  have hTime (h : BitString n) (t : BitString m) :
      time (Fin.append h t) = BitString.equivBitVec t :=
    congrArg BitString.equivBitVec (funext fun i => Fin.append_right _ _ i)
  have hDepth {h : BitString n} (hh : h ∈ H) (t : BitString m) :
      htWord (Fin.append h t) = BitString.equivBitVec (bitCode (depthCode f h)) := by
    simp only [htWord, hStart, hdep hh]
  have hmod {q : ℕ} (hq : q < 2 ^ n ∨ q < 2 ^ m) : q % 2 ^ (n + m) = q :=
    Nat.mod_eq_of_lt (hq.elim (fun h => h.trans_le (Nat.pow_le_pow_right (by decide) (by lia)))
      fun h => h.trans_le (Nat.pow_le_pow_right (by decide) (by lia)))
  refine ⟨out, fun h hh t => ?_, fun h hh t htrans => ?_, hs⟩
  · rw [heval]
    change flag (Fin.append h t) = _
    simp only [flag, hTime, hDepth hh, BitVec.ult, BitVec.toNat_setWidth, code_toNat,
      hmod (Or.inr (BitString.equivBitVec t).isLt), hmod (Or.inl (depthCode f h).isLt)]
    rfl
  · rw [heval]
    change result (Fin.append h t) = _
    let u := (BitString.equivBitVec t).toNat
    have htrunc : (BitString.equivBitVec t).toNat % 2 ^ n = u :=
      Nat.mod_eq_of_lt (htrans.trans (depthCode f h).isLt)
    have htarget : (target (Fin.append h t)).val = transientDepth f h - u := by
      change (targetWord (Fin.append h t)).toNat = _
      simp only [targetWord, hTime, hDepth hh]
      rw [BitVec.toNat_sub_of_le (by
        simpa only [BitVec.le_def, code_toNat, BitVec.toNat_setWidth, htrunc, depthCode] using
          htrans.le)]
      simp only [code_toNat, BitVec.toNat_setWidth, htrunc, depthCode]
    conv_rhs => rw [← hStart h t]
    refine hresult (Fin.append h t) u
      (by simp only [v, hStart, hpre hh, bitCode, Equiv.apply_symm_apply]; rfl)
      (by rwa [hStart]) (by rwa [hStart]) ?_
    obtain ⟨y, hy, ha, hl, hb⟩ : ∃ y ∈ H, (∃ j ≤ transientDepth f h, f^[j] h = y) ∧
        transientDepth f h - u ≤ transientDepth f y ∧
        transientDepth f y ≤ transientDepth f h - u + K :=
      if short : u ≤ K then ⟨h, hh, ⟨0, Nat.zero_le _, rfl⟩, Nat.sub_le _ _, by lia⟩
      else hcover h hh u (Nat.lt_of_not_ge short) htrans
    exact ⟨equiv ⟨y, hy⟩, by simpa only [marks, Equiv.symm_apply_apply, hStart, htarget] using
      ⟨ha, hl, hb⟩⟩

end Cslib.Circuits.Boolean.Iteration
