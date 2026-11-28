/-
Copyright (c) 2026 Samuel Schlesinger, Olivia Daniels. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Olivia Daniels
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.CookLevin.Quasilinear.Bounds
public import CslibFrontier.Computability.Complexity.CookLevin.Quasilinear.Defining
public import CslibFrontier.Computability.Complexity.CookLevin.Quasilinear.Decode
import CslibFrontier.Foundations.Data.List.FlatMapRange

/-!
# Structure of the constraint gadgets of the quasilinear formula

The constraints of `Cslib.Complexity.CookLevin.Quasilinear.Layout` come in nine families. This file
proves what the rest of the reduction needs to know about them: there are at most `MAXI`
constraints per family, a constraint has at most `8` assertion gates, the gates defining its fresh
variables number at most `A R`, so that the blocks of fresh variables of different constraints do
not overlap, and these gates define their variables in order from smaller ones. The machine data
read from a machine fits its layout (`MachineData.Fits`).

## Main results

* `Cslib.Complexity.CookLevin.Quasilinear.Layout.count_le_MAXI`,
  `Layout.length_famCons_le`, `Layout.length_famDefs_le`.
* `Cslib.Complexity.CookLevin.Quasilinear.Layout.defining_famDefs`.
* `Cslib.Complexity.CookLevin.Quasilinear.machineData_fits`.
-/

public section

namespace Cslib.Complexity.CookLevin.Quasilinear

open Turing Cslib.BitonicSort

/-- The data of a machine fits a layout: state codes have `S` bits and patterns `2 C` bits. -/
structure MachineData.Fits (Λ : Layout) (D : MachineData) : Prop where
  /-- the bits of the initial state -/
  q0 : D.q0.length = Λ.S
  /-- the bits of the halted state -/
  halt : D.halt.length = Λ.S
  /-- the bits of the allowed pairs -/
  pairs : ∀ bs ∈ D.pairs, bs.length = 2 * Λ.C

namespace Layout

variable (Λ : Layout)

/-- The fresh variables start at `8` or later. -/
private theorem eight_le_AUX : 8 ≤ Λ.AUX := by unfold AUX; omega

/-- The constraints of each family are at most `MAXI`. -/
theorem count_le_MAXI (fam : Family) : Λ.count fam ≤ Λ.MAXI := by
  have hN := Λ.two_le_N
  have hI : 2 ≤ Λ.I := by unfold I; omega
  have hM : Λ.MAXI = (Λ.N * Λ.I * ((Λ.k + 1) * (Λ.L + 1) * (Λ.P + 1))) * 3 := by
    unfold MAXI; ring
  have hQ : 0 < (Λ.k + 1) * (Λ.L + 1) * (Λ.P + 1) := by positivity
  have hNI : Λ.N * 1 ≤ Λ.N * Λ.I := Nat.mul_le_mul_left _ (by omega)
  have hbig : Λ.N * Λ.I * 1 ≤ Λ.N * Λ.I * ((Λ.k + 1) * (Λ.L + 1) * (Λ.P + 1)) :=
    Nat.mul_le_mul_left _ hQ
  cases fam <;> simp only [count]
  · rw [hM]; nlinarith
  · rw [hM]; nlinarith
  · rw [hM]; nlinarith
  · rw [hM]; have : Λ.N - 1 ≤ Λ.N := Nat.sub_le _ _; nlinarith
  · rw [hM]
    have : (Λ.N - 1) * Λ.I ≤ Λ.N * Λ.I := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    nlinarith
  · rw [hM]; nlinarith
  · rw [hM]
    have h1 : (Λ.N - 1) * Λ.k ≤ Λ.N * (Λ.k + 1) :=
      Nat.mul_le_mul (Nat.sub_le _ _) (by omega)
    have h2 : Λ.N * (Λ.k + 1) ≤ Λ.N * Λ.I * ((Λ.k + 1) * (Λ.L + 1) * (Λ.P + 1)) := by
      calc Λ.N * (Λ.k + 1) = Λ.N * 1 * (Λ.k + 1) := by ring
        _ ≤ Λ.N * Λ.I * ((Λ.k + 1) * (Λ.L + 1) * (Λ.P + 1)) :=
          Nat.mul_le_mul hNI (by
            calc Λ.k + 1 = (Λ.k + 1) * 1 * 1 := by ring
              _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega))
    omega
  · rw [hM]
    have h1 : Λ.k * Λ.L * Λ.N * Λ.P ≤ (Λ.k + 1) * (Λ.L + 1) * (Λ.P + 1) * Λ.N := by
      calc Λ.k * Λ.L * Λ.N * Λ.P ≤ (Λ.k + 1) * (Λ.L + 1) * Λ.N * (Λ.P + 1) := by
            gcongr <;> omega
        _ = _ := by ring
    have h2 : (Λ.k + 1) * (Λ.L + 1) * (Λ.P + 1) * Λ.N ≤
        Λ.N * Λ.I * ((Λ.k + 1) * (Λ.L + 1) * (Λ.P + 1)) := by
      calc (Λ.k + 1) * (Λ.L + 1) * (Λ.P + 1) * Λ.N
          = ((Λ.k + 1) * (Λ.L + 1) * (Λ.P + 1)) * (Λ.N * 1) := by ring
        _ ≤ ((Λ.k + 1) * (Λ.L + 1) * (Λ.P + 1)) * (Λ.N * Λ.I) :=
          Nat.mul_le_mul_left _ hNI
        _ = _ := by ring
    omega
  · rw [hM]
    have h1 : Λ.k * Λ.N ≤ (Λ.k + 1) * Λ.N := Nat.mul_le_mul_right _ (by omega)
    have h2 : (Λ.k + 1) * Λ.N ≤ Λ.N * Λ.I * ((Λ.k + 1) * (Λ.L + 1) * (Λ.P + 1)) := by
      calc (Λ.k + 1) * Λ.N = ((Λ.k + 1) * 1 * 1) * (Λ.N * 1) := by ring
        _ ≤ ((Λ.k + 1) * (Λ.L + 1) * (Λ.P + 1)) * (Λ.N * Λ.I) :=
          Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)) hNI
        _ = _ := by ring
    omega

/-- A constraint has at most eight assertion gates. -/
theorem length_famCons_le (D : MachineData) (x : List Bool) (fam : Family) (inst : ℕ) :
    (Λ.famCons D x fam inst).length ≤ 8 := by
  cases fam <;> simp only [famCons, List.length_cons, List.length_nil] <;> (try split) <;>
    (try simp only [List.length_cons, List.length_nil]) <;> omega

/-- The finite part fits in a record. -/
theorem C_le_RB : Λ.C ≤ Λ.RB := by unfold RB; omega

/-- The input-head position fits in a record. -/
private theorem C_add_I_le_RB : Λ.C + Λ.I ≤ Λ.RB := by unfold RB; omega

/-- The position of work head `j` fits in a record. -/
private theorem offPos_add_W_le_RB {j : ℕ} (hj : j < Λ.k) : Λ.offPos j + Λ.W ≤ Λ.RB := by
  have h1 : Λ.W * j + Λ.W ≤ Λ.W * Λ.k := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hj
  have h2 := Nat.mul_comm Λ.k Λ.W
  unfold offPos RB
  omega

/-- The bits of work tape `j` fit in the finite part. -/
private theorem offTape_add_le_C {j : ℕ} (hj : j < Λ.k) : Λ.offTape j + 8 ≤ Λ.C := by
  unfold offTape C; omega

/-- Literals about the bits of a record in range are below the fresh variables. -/
private theorem fieldLits_lt {t off : ℕ} {bs : List Bool} (ht : t < Λ.N)
    (h : off + bs.length ≤ Λ.RB) :
    ∀ l ∈ Λ.fieldLits t off bs, l.1 < Λ.AUX := by
  intro l hl
  simp only [fieldLits, List.mem_map, List.mem_range] at hl
  obtain ⟨i, hi, rfl⟩ := hl
  exact Λ.vRec_lt_AUX ht (by omega)

/-- The number of literals about a field. -/
@[simp] theorem length_fieldLits (t off : ℕ) (bs : List Bool) :
    (Λ.fieldLits t off bs).length = bs.length := by simp [fieldLits]

variable (D : MachineData) (x : List Bool)

/-- The length of the literals of the first record. -/
private theorem length_initLits (hD : D.Fits Λ) :
    (Λ.initLits D).length = Λ.S + Λ.I + Λ.k * Λ.W + 2 := by
  have h := List.length_flatMap_range (α := ℕ × Bool)
    (T := fun j => Λ.fieldLits 0 (Λ.offPos j) (BitString.lowBits Λ.W Λ.N)) (K := Λ.W)
    (fun _ => by simp) Λ.k
  simp only [initLits, List.length_append, length_fieldLits, BitString.length_lowBits, length_two,
    hD.q0, h]
  rw [Nat.mul_comm Λ.W]

/-- The length of the literals of the last record. -/
private theorem length_finalLits (hD : D.Fits Λ) : (Λ.finalLits D).length = Λ.S + 2 := by
  simp only [finalLits, List.length_append, length_fieldLits, length_two, hD.halt]

/-- The literals of the first record are below the fresh variables. -/
private theorem initLits_lt (hD : D.Fits Λ) : ∀ l ∈ Λ.initLits D, l.1 < Λ.AUX := by
  have hN := Λ.two_le_N
  have hC := Λ.C_le_RB
  have hCI := Λ.C_add_I_le_RB
  have hS : Λ.S + 8 ≤ Λ.C := by unfold C; omega
  intro l hl
  simp only [initLits, List.mem_append, List.mem_flatMap, List.mem_range] at hl
  rcases hl with ((hl | hl) | ⟨j, hj, hl⟩) | hl
  · exact Λ.fieldLits_lt (by omega) (by rw [hD.q0]; omega) l hl
  · exact Λ.fieldLits_lt (by omega) (by simp only [BitString.length_lowBits, offIn]; omega) l hl
  · exact Λ.fieldLits_lt (by omega) (by
      simp only [BitString.length_lowBits]; exact Λ.offPos_add_W_le_RB hj) l hl
  · exact Λ.fieldLits_lt (by omega) (by simp only [length_two]; omega) l hl

/-- The literals of the last record are below the fresh variables. -/
private theorem finalLits_lt (hD : D.Fits Λ) : ∀ l ∈ Λ.finalLits D, l.1 < Λ.AUX := by
  have hN := Λ.two_le_N
  have hC := Λ.C_le_RB
  have hS : Λ.S + 8 ≤ Λ.C := by unfold C; omega
  intro l hl
  simp only [finalLits, List.mem_append] at hl
  rcases hl with hl | hl
  · exact Λ.fieldLits_lt (by omega) (by rw [hD.halt]; omega) l hl
  · exact Λ.fieldLits_lt (by omega) (by simp only [length_two]; omega) l hl

/-- The gates defining the fresh variables of a constraint number at most `A R`. -/
theorem length_famDefs_le (hD : D.Fits Λ) (fam : Family) (inst : ℕ) :
    (Λ.famDefs D x fam inst).length ≤ Λ.A D.pairs.length := by
  have hA : Λ.A D.pairs.length = 2 * (Λ.S + Λ.I + Λ.k * Λ.W + 2) + 4 * Λ.C * D.pairs.length +
      D.pairs.length + 4 * Λ.I + 4 + 9 * Λ.W + 5 * (Λ.τ + Λ.W) + 2 * Λ.W + 4 := rfl
  have hpl : (Λ.stepPats D inst).length = D.pairs.length := by simp [stepPats]
  have hmul : 2 * (2 * Λ.C) * D.pairs.length = 4 * Λ.C * D.pairs.length := by ring
  cases fam <;> simp only [famDefs]
  all_goals try split_ifs
  · simp only [List.length_cons, List.length_nil]; omega
  · rw [length_matchGadget, length_initLits Λ D hD]; omega
  · rw [length_matchGadget, length_finalLits Λ D hD]; omega
  · rw [length_tableGadget _ _ _ _ (pats := Λ.stepPats D inst) (by
      intro π hπ
      simp only [stepPats, List.mem_map] at hπ
      obtain ⟨_, _, rfl⟩ := hπ
      simp), hpl, hmul]
    omega
  · simp only [List.length_append, length_matchGadget, inMoveLits, inNextLits, length_fieldLits,
      BitString.length_lowBits, length_two]
    omega
  · simp only [List.length_append, length_matchGadget, inAtLits, inSymLits, length_fieldLits,
      BitString.length_lowBits, length_two]
    omega
  · simp only [length_addGadget, posPairs, List.length_map, List.length_range]
    omega
  · simp only [List.length_nil]; omega
  · simp only [List.length_cons, List.length_nil]; omega
  · simp only [List.length_append, length_ltGadget, length_eqGadget, keyPairs, samePairs,
      List.length_map, List.length_range, List.length_cons, List.length_nil]
    omega

/-- The block of fresh variables of a constraint ends below `AUX + 9 * MAXI * A R`. -/
private theorem vAux_add_A_le (R : ℕ) {fam : Family} {inst : ℕ} (hinst : inst < Λ.count fam) :
    Λ.vAux R fam inst 0 + Λ.A R ≤ Λ.AUX + 9 * Λ.MAXI * Λ.A R := by
  have hcm := Λ.count_le_MAXI fam
  have hf := fam.index_lt
  have h0 : fam.index * Λ.MAXI ≤ 8 * Λ.MAXI := Nat.mul_le_mul_right _ (by omega)
  have h2 : (fam.index * Λ.MAXI + inst + 1) * Λ.A R ≤ 9 * Λ.MAXI * Λ.A R :=
    Nat.mul_le_mul_right _ (by omega)
  have h3 : (fam.index * Λ.MAXI + inst + 1) * Λ.A R =
      (fam.index * Λ.MAXI + inst) * Λ.A R + Λ.A R :=
    Nat.succ_mul _ _
  unfold vAux
  omega

/-- The gates defining the fresh variables of a constraint define them in order, from smaller
variables, so any assignment of the primary variables extends. -/
theorem defining_famDefs (hD : D.Fits Λ) {fam : Family} {inst : ℕ}
    (hinst : inst < Λ.count fam) :
    Defining (Λ.vAux D.pairs.length fam inst 0) (Λ.famDefs D x fam inst) := by
  have hβ : Λ.AUX ≤ Λ.vAux D.pairs.length fam inst 0 := by unfold vAux; omega
  have h8 := Λ.eight_le_AUX
  have hN := Λ.two_le_N
  have hC := Λ.C_le_RB
  have hCI := Λ.C_add_I_le_RB
  have hS : Λ.S + 8 ≤ Λ.C := by unfold C; omega
  have hI : 2 ≤ Λ.I := by unfold I; omega
  have hI0 : 0 < Λ.I := by omega
  have hN0 : 0 < Λ.N := by omega
  have hP : Λ.P = Λ.τ + Λ.W + 4 := rfl
  have hW : Λ.W = Λ.τ + 2 := rfl
  cases fam
  · simp only [famDefs]
    generalize Λ.vAux D.pairs.length .consts inst 0 = β at hβ ⊢
    simp only [defining_cons_iff, defining_nil, Gate.Op.IsDefining, ne_eq, reduceCtorEq,
      not_false_eq_true, and_true, true_and, vFF]
    omega
  · simp only [famDefs]
    generalize Λ.vAux D.pairs.length .init inst 0 = β at hβ ⊢
    exact defining_matchGadget (fun l hl => by have := Λ.initLits_lt D hD l hl; omega)
      (by unfold vTT; omega)
  · simp only [famDefs]
    generalize Λ.vAux D.pairs.length .final inst 0 = β at hβ ⊢
    exact defining_matchGadget (fun l hl => by have := Λ.finalLits_lt D hD l hl; omega)
      (by unfold vTT; omega)
  · change inst < Λ.N - 1 at hinst
    simp only [famDefs]
    generalize Λ.vAux D.pairs.length .step inst 0 = β at hβ ⊢
    refine defining_tableGadget (fun π hπ => ?_) (by unfold vTT; omega) (by unfold vFF; omega)
    simp only [stepPats, List.mem_map] at hπ
    obtain ⟨bs, -, rfl⟩ := hπ
    refine ⟨by simp, fun l hl => ?_⟩
    simp only [List.mem_map, List.mem_range] at hl
    obtain ⟨i, hi, rfl⟩ := hl
    dsimp only
    split_ifs with h
    · exact lt_of_lt_of_le (Λ.vRec_lt_AUX (by omega) (by omega)) hβ
    · exact lt_of_lt_of_le (Λ.vRec_lt_AUX (by omega) (by omega)) hβ
  · change inst < (Λ.N - 1) * Λ.I * 3 at hinst
    have h1 : inst / 3 < (Λ.N - 1) * Λ.I := (Nat.div_lt_iff_lt_mul (by norm_num)).2 hinst
    have ht : inst / 3 / Λ.I < Λ.N - 1 := (Nat.div_lt_iff_lt_mul hI0).2 h1
    simp only [famDefs]
    generalize Λ.vAux D.pairs.length .inMove inst 0 = β at hβ ⊢
    generalize inst / 3 / Λ.I = t at ht ⊢
    generalize inst / 3 % Λ.I = z
    generalize inst % 3 = m
    have hA : ∀ l ∈ Λ.inMoveLits t z m, l.1 < β := by
      intro l hl
      simp only [inMoveLits, List.mem_append] at hl
      rcases hl with hl | hl
      · have := Λ.fieldLits_lt (by omega)
          (by simp only [BitString.length_lowBits, offIn]; omega) l hl
        omega
      · have := Λ.fieldLits_lt (by omega) (by simp only [length_two]; omega) l hl
        omega
    refine defining_append (defining_matchGadget hA (by unfold vTT; omega)) ?_
    rw [length_matchGadget]
    refine defining_matchGadget (fun l hl => ?_) (by unfold vTT; omega)
    simp only [inNextLits] at hl
    have := Λ.fieldLits_lt (by omega) (by simp only [BitString.length_lowBits, offIn]; omega) l hl
    omega
  · change inst < Λ.N * Λ.I at hinst
    have ht : inst / Λ.I < Λ.N := (Nat.div_lt_iff_lt_mul hI0).2 hinst
    simp only [famDefs]
    generalize Λ.vAux D.pairs.length .inSym inst 0 = β at hβ ⊢
    generalize inst / Λ.I = t at ht ⊢
    generalize inst % Λ.I = z
    have hA : ∀ l ∈ Λ.inAtLits t z, l.1 < β := by
      intro l hl
      have := Λ.fieldLits_lt (by omega) (by simp only [BitString.length_lowBits, offIn]; omega) l hl
      omega
    refine defining_append (defining_matchGadget hA (by unfold vTT; omega)) ?_
    rw [length_matchGadget]
    refine defining_matchGadget (fun l hl => ?_) (by unfold vTT; omega)
    simp only [inSymLits] at hl
    have := Λ.fieldLits_lt (by omega) (by simp only [length_two]; omega) l hl
    omega
  · change inst < (Λ.N - 1) * Λ.k at hinst
    have hk : 0 < Λ.k := Nat.pos_of_ne_zero (fun h => by simp [h] at hinst)
    have ht : inst / Λ.k < Λ.N - 1 := (Nat.div_lt_iff_lt_mul hk).2 hinst
    have hj : inst % Λ.k < Λ.k := Nat.mod_lt _ hk
    simp only [famDefs]
    generalize Λ.vAux D.pairs.length .workMove inst 0 = β at hβ ⊢
    generalize inst / Λ.k = t at ht ⊢
    generalize inst % Λ.k = j at hj ⊢
    have hT := Λ.offTape_add_le_C hj
    refine defining_addGadget (fun p hp => ?_) (by unfold vTT; omega) ?_ ?_
    · simp only [posPairs, List.mem_map, List.mem_range] at hp
      obtain ⟨i, hi, rfl⟩ := hp
      have := Λ.offPos_add_W_le_RB hj
      exact ⟨lt_of_lt_of_le (Λ.vRec_lt_AUX (by omega) (by omega)) hβ,
        lt_of_lt_of_le (Λ.vRec_lt_AUX (by omega) (by omega)) hβ⟩
    · exact lt_of_lt_of_le (Λ.vRec_lt_AUX (by omega) (by unfold offTape at hT ⊢; omega)) hβ
    · exact lt_of_lt_of_le (Λ.vRec_lt_AUX (by omega) (by unfold offTape at hT ⊢; omega)) hβ
  · simp only [famDefs]
    exact defining_nil _
  · change inst < Λ.k * Λ.N at hinst
    have hj : inst / Λ.N < Λ.k := (Nat.div_lt_iff_lt_mul hN0).2 hinst
    have hu : inst % Λ.N < Λ.N := Nat.mod_lt _ hN0
    simp only [famDefs]
    generalize Λ.vAux D.pairs.length .sorted inst 0 = β at hβ ⊢
    generalize inst / Λ.N = j at hj ⊢
    generalize inst % Λ.N = u at hu ⊢
    by_cases h0 : u = 0
    · rw [ite_eq_left h0]
      have a1 := Λ.arrAt_lt_AUX (j := j) (ℓ := Λ.L) (w := 0) (b := Λ.τ + Λ.W) hj le_rfl
        (by omega) (by omega)
      have a2 := Λ.arrAt_lt_AUX (j := j) (ℓ := Λ.L) (w := 0) (b := Λ.τ + Λ.W + 1) hj le_rfl
        (by omega) (by omega)
      simp only [defining_cons_iff, defining_nil, Gate.Op.IsDefining, ne_eq, reduceCtorEq,
        not_false_eq_true, and_true, true_and]
      omega
    · rw [ite_eq_right h0]
      have hkp : ∀ p ∈ Λ.keyPairs j u, p.1 < β ∧ p.2 < β := by
        intro p hp
        simp only [keyPairs, List.mem_map, List.mem_range] at hp
        obtain ⟨b, hb, rfl⟩ := hp
        exact ⟨lt_of_lt_of_le (Λ.arrAt_lt_AUX hj le_rfl (by omega) (by omega)) hβ,
          lt_of_lt_of_le (Λ.arrAt_lt_AUX hj le_rfl (by omega) (by omega)) hβ⟩
      have hsp : ∀ p ∈ Λ.samePairs j u, p.1 < β ∧ p.2 < β := by
        intro p hp
        simp only [samePairs, List.mem_map, List.mem_range] at hp
        obtain ⟨b, hb, rfl⟩ := hp
        exact ⟨lt_of_lt_of_le (Λ.arrAt_lt_AUX hj le_rfl (by omega) (by omega)) hβ,
          lt_of_lt_of_le (Λ.arrAt_lt_AUX hj le_rfl (by omega) (by omega)) hβ⟩
      have a1 := Λ.arrAt_lt_AUX (j := j) (ℓ := Λ.L) (w := u) (b := Λ.τ + Λ.W) hj le_rfl
        hu (by omega)
      have a2 := Λ.arrAt_lt_AUX (j := j) (ℓ := Λ.L) (w := u) (b := Λ.τ + Λ.W + 1) hj le_rfl
        hu (by omega)
      have a3 := Λ.arrAt_lt_AUX (j := j) (ℓ := Λ.L) (w := u - 1) (b := Λ.τ + Λ.W + 2) hj
        le_rfl
        (by omega) (by omega)
      have a4 := Λ.arrAt_lt_AUX (j := j) (ℓ := Λ.L) (w := u - 1) (b := Λ.τ + Λ.W + 3) hj
        le_rfl
        (by omega) (by omega)
      have e1 : (ltGadget β vFF (Λ.keyPairs j u)).length = 5 * (Λ.τ + Λ.W) := by
        simp [keyPairs]
      have e2 : (eqGadget (β + 5 * (Λ.τ + Λ.W)) vTT (Λ.samePairs j u)).length = 2 * Λ.W := by
        simp [samePairs]
      refine defining_append (defining_append (defining_ltGadget hkp (by unfold vFF; omega)) ?_) ?_
      · rw [e1]
        exact defining_eqGadget (fun p hp => by have := hsp p hp; omega) (by unfold vTT; omega)
      · rw [List.length_append, e1, e2]
        simp only [defining_cons_iff, defining_nil, Gate.Op.IsDefining, ne_eq, reduceCtorEq,
        not_false_eq_true, and_true, true_and]
        omega

/-- The assertion gates of a constraint only mention variables below the end of the fresh
variables. -/
private theorem vars_famCons_lt (hD : D.Fits Λ) {fam : Family} {inst : ℕ}
    (hinst : inst < Λ.count fam) {g : Gate} (hg : g ∈ Λ.famCons D x fam inst) :
    g.out < Λ.AUX + 9 * Λ.MAXI * Λ.A D.pairs.length ∧
      g.a < Λ.AUX + 9 * Λ.MAXI * Λ.A D.pairs.length ∧
      g.b < Λ.AUX + 9 * Λ.MAXI * Λ.A D.pairs.length ∧
      g.c < Λ.AUX + 9 * Λ.MAXI * Λ.A D.pairs.length := by
  have hA : Λ.A D.pairs.length = 2 * (Λ.S + Λ.I + Λ.k * Λ.W + 2) + 4 * Λ.C * D.pairs.length +
      D.pairs.length + 4 * Λ.I + 4 + 9 * Λ.W + 5 * (Λ.τ + Λ.W) + 2 * Λ.W + 4 := rfl
  have hβB := Λ.vAux_add_A_le D.pairs.length hinst
  have hβ : Λ.AUX ≤ Λ.vAux D.pairs.length fam inst 0 := by unfold vAux; omega
  have h8 := Λ.eight_le_AUX
  have hN := Λ.two_le_N
  have hI : 2 ≤ Λ.I := by unfold I; omega
  have hI0 : 0 < Λ.I := by omega
  have hN0 : 0 < Λ.N := by omega
  have hP : Λ.P = Λ.τ + Λ.W + 4 := rfl
  have hW : Λ.W = Λ.τ + 2 := rfl
  revert g
  cases fam
  · simp only [famCons]
    generalize Λ.vAux D.pairs.length .consts inst 0 = β at hβ hβB ⊢
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros <;>
      (try simp only [vTT]) <;> omega
  · have hl := Λ.length_initLits D hD
    simp only [famCons]
    generalize Λ.vAux D.pairs.length .init inst 0 = β at hβ hβB ⊢
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]
    and_intros <;>
      (try simp only [matchOut, vTT]) <;>
      (try split_ifs) <;> omega
  · have hl := Λ.length_finalLits D hD
    simp only [famCons]
    generalize Λ.vAux D.pairs.length .final inst 0 = β at hβ hβB ⊢
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]
    and_intros <;>
      (try simp only [matchOut, vTT]) <;>
      (try split_ifs) <;> omega
  · have hpl : (Λ.stepPats D inst).length = D.pairs.length := by simp [stepPats]
    have hmul : 2 * (2 * Λ.C) * (Λ.stepPats D inst).length = 4 * Λ.C * D.pairs.length := by
      rw [hpl]; ring
    simp only [famCons]
    generalize Λ.vAux D.pairs.length .step inst 0 = β at hβ hβB ⊢
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]
    and_intros <;>
      (try simp only [tableOut, vFF]) <;>
      (try split_ifs) <;> omega
  · have l1 : (Λ.inMoveLits (inst / 3 / Λ.I) (inst / 3 % Λ.I) (inst % 3)).length =
        Λ.I + 2 := by
      simp [inMoveLits]
    have l2 : (Λ.inNextLits (inst / 3 / Λ.I) (inst / 3 % Λ.I) (inst % 3)).length = Λ.I := by
      simp [inNextLits]
    simp only [famCons]
    generalize Λ.vAux D.pairs.length .inMove inst 0 = β at hβ hβB ⊢
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]
    and_intros <;>
      (try simp only [matchOut, vTT]) <;>
      (try split_ifs) <;> omega
  · have l1 : (Λ.inAtLits (inst / Λ.I) (inst % Λ.I)).length = Λ.I := by
      simp [inAtLits]
    have l2 : (Λ.inSymLits x (inst / Λ.I) (inst % Λ.I)).length = 2 := by
      simp [inSymLits]
    simp only [famCons]
    generalize Λ.vAux D.pairs.length .inSym inst 0 = β at hβ hβB ⊢
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]
    and_intros <;>
      (try simp only [matchOut, vTT]) <;>
      (try split_ifs) <;> omega
  · simp only [famCons]
    generalize Λ.vAux D.pairs.length .workMove inst 0 = β at hβ hβB ⊢
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]
    and_intros <;>
      (try simp only [addOut, vTT]) <;>
      (try split_ifs) <;> omega
  · change inst < Λ.k * Λ.L * Λ.N * Λ.P at hinst
    have hP0 : 0 < Λ.P := by omega
    have hb : inst % Λ.P < Λ.P := Nat.mod_lt _ hP0
    have h1 : inst / Λ.P < Λ.k * Λ.L * Λ.N := (Nat.div_lt_iff_lt_mul hP0).2 hinst
    have hw : inst / Λ.P % Λ.N < Λ.N := Nat.mod_lt _ hN0
    have h2 : inst / Λ.P / Λ.N < Λ.k * Λ.L := (Nat.div_lt_iff_lt_mul hN0).2 h1
    have hL0 : 0 < Λ.L := Nat.pos_of_ne_zero (fun h => by simp [h] at h2)
    have hℓ : inst / Λ.P / Λ.N % Λ.L < Λ.L := Nat.mod_lt _ hL0
    have hj : inst / Λ.P / Λ.N / Λ.L < Λ.k := (Nat.div_lt_iff_lt_mul hL0).2 h2
    have he := Λ.expo_lt hℓ
    simp only [famCons]
    generalize inst % Λ.P = b at hb ⊢
    generalize inst / Λ.P % Λ.N = w at hw ⊢
    generalize inst / Λ.P / Λ.N % Λ.L = ℓ at hℓ he ⊢
    generalize inst / Λ.P / Λ.N / Λ.L = j at hj ⊢
    have a1 := Λ.arrAt_lt_AUX hj (by omega : ℓ + 1 ≤ Λ.L) hw hb
    have a2 := Λ.arrAt_lt_AUX hj (by omega : ℓ ≤ Λ.L) (partner_lt he hw) hb
    have a3 := Λ.arrAt_lt_AUX hj (by omega : ℓ ≤ Λ.L) hw hb
    have a4 := Λ.vFlag_lt_AUX hj hℓ (lt_of_le_of_lt (low_le (Λ.expo ℓ) w) hw)
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]
    and_intros <;> omega
  · change inst < Λ.k * Λ.N at hinst
    have hj : inst / Λ.N < Λ.k := (Nat.div_lt_iff_lt_mul hN0).2 hinst
    have hu : inst % Λ.N < Λ.N := Nat.mod_lt _ hN0
    simp only [famCons]
    generalize Λ.vAux D.pairs.length .sorted inst 0 = β at hβ hβB ⊢
    generalize inst / Λ.N = j at hj ⊢
    generalize inst % Λ.N = u at hu ⊢
    intro g
    by_cases h0 : u = 0
    · rw [ite_eq_left h0]
      revert g
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      and_intros <;> omega
    · rw [ite_eq_right h0]
      revert g
      have a1 := Λ.arrAt_lt_AUX (j := j) (ℓ := Λ.L) (w := u) (b := Λ.τ + Λ.W) hj le_rfl
        hu (by omega)
      have a2 := Λ.arrAt_lt_AUX (j := j) (ℓ := Λ.L) (w := u) (b := Λ.τ + Λ.W + 1) hj le_rfl
        hu (by omega)
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      and_intros <;>
      (try simp only [ltOut, eqOut, vTT, vFF]) <;>
      (try split_ifs) <;> omega

/-- **Every variable of every gate of a constraint is below the end of the fresh variables.** -/
theorem vars_famGates_lt (hD : D.Fits Λ) {fam : Family} {inst : ℕ}
    (hinst : inst < Λ.count fam) {g : Gate} (hg : g ∈ Λ.famGates D x fam inst) :
    g.out < Λ.AUX + 9 * Λ.MAXI * Λ.A D.pairs.length ∧
      g.a < Λ.AUX + 9 * Λ.MAXI * Λ.A D.pairs.length ∧
      g.b < Λ.AUX + 9 * Λ.MAXI * Λ.A D.pairs.length ∧
      g.c < Λ.AUX + 9 * Λ.MAXI * Λ.A D.pairs.length := by
  have hβB := Λ.vAux_add_A_le D.pairs.length hinst
  unfold famGates at hg
  rcases List.mem_append.1 hg with hg | hg
  · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hg
    obtain ⟨-, h2, h3, h4, h5⟩ := Λ.defining_famDefs D x hD hinst i hi
    have hlen := Λ.length_famDefs_le D x hD fam inst
    refine ⟨?_, ?_, ?_, ?_⟩ <;> omega
  · exact Λ.vars_famCons_lt D x hD hinst hg

end Layout

/-- The data read from a machine fits the layout of the machine. -/
theorem machineData_fits {k : ℕ} {State : Type} [Fintype State]
    (ntm : Turing.MultiTapeNTM k Bool State) (κ n : ℕ) :
    (machineData ntm).Fits (layoutOf k State κ n) where
  q0 := by
    change ((List.range (stWidth State)).map _).length = stWidth State
    simp
  halt := by
    change ((List.range (stWidth State)).map _).length = stWidth State
    simp
  pairs := by
    intro bs hbs
    simp only [machineData, List.mem_map] at hbs
    obtain ⟨p, -, rfl⟩ := hbs
    change (pairBits p.1 p.2).length = 2 * ctrlWidth k State
    simp [pairBits]

end Cslib.Complexity.CookLevin.Quasilinear
