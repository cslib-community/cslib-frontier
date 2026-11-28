/-
Copyright (c) 2026 Samuel Schlesinger, Olivia Daniels. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Olivia Daniels
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.CookLevin.Quasilinear.Completeness
public import CslibFrontier.Computability.Complexity.CookLevin.Quasilinear.Structure

/-!
# The quasilinear formula is satisfiable exactly when the machine accepts

The constraints of the quasilinear formula of a machine `ntm` on an input `x` can all be satisfied
(`Layout.Sat`) exactly when `ntm` accepts `x`, as soon as `ntm` runs within fewer than `N` steps
(`Layout.sat_iff_accepts`).

One direction is `accepts_of_sat`. For the other, a valid sequence of records gives an
assignment of every variable below the fresh ones whose statements all hold
(`Layout.meaning_of_valid`); the fresh variables of each constraint are then given the values their
defining gates compute (`exists_extension`), which makes every defining gate hold, and
then every assertion (`Layout.forall_famCons_iff`).

## Main results

* `Cslib.Complexity.CookLevin.Quasilinear.Layout.exists_sat_of_valid`.
* `Cslib.Complexity.CookLevin.Quasilinear.Layout.exists_sat_of_accepts`.
* `Cslib.Complexity.CookLevin.Quasilinear.Layout.sat_iff_accepts`.
-/

@[expose] public section

namespace Cslib.Complexity.CookLevin.Quasilinear

open Turing

namespace Layout

variable (Λ : Layout) (D : MachineData) (x : List Bool)

/-- The gate defining a fresh variable: gate `r % A` of constraint `r / A % MAXI` of family
number `r / A / MAXI`, where `r` is the offset of the variable from the first fresh one. -/
private def dfnOf (v : ℕ) : Option Gate :=
  if Λ.AUX ≤ v then
    match Family.ofIndex? ((v - Λ.AUX) / Λ.A D.pairs.length / Λ.MAXI) with
    | some fam =>
      if (v - Λ.AUX) / Λ.A D.pairs.length % Λ.MAXI < Λ.count fam then
        (Λ.famDefs D x fam ((v - Λ.AUX) / Λ.A D.pairs.length % Λ.MAXI))[
          (v - Λ.AUX) % Λ.A D.pairs.length]?
      else none
    | none => none
  else none

/-- A variable below the fresh ones is defined by no gate. -/
private theorem dfnOf_eq_none {v : ℕ} (hv : v < Λ.AUX) : Λ.dfnOf D x v = none := by
  unfold dfnOf
  rw [ite_eq_right (by omega)]

/-- The defining gate of a fresh variable defines it from smaller variables. -/
private theorem dfnOf_spec (hD : D.Fits Λ) {v : ℕ} {g : Gate} (h : Λ.dfnOf D x v = some g) :
    g.op.IsDefining ∧ g.out = v ∧ g.a < v ∧ g.b < v ∧ g.c < v := by
  unfold dfnOf at h
  split_ifs at h with hv
  split at h
  next fam hfam =>
    split_ifs at h with hinst
    obtain ⟨hi, hg⟩ := List.getElem?_eq_some_iff.1 h
    have hdef := Λ.defining_famDefs D x hD hinst _ hi
    rw [hg] at hdef
    obtain ⟨h1, h2, h3, h4, h5⟩ := hdef
    set r := v - Λ.AUX
    set A := Λ.A D.pairs.length
    have hv' : Λ.vAux D.pairs.length fam (r / A % Λ.MAXI) 0 + r % A = v := by
      unfold vAux
      rw [Family.index_eq_of_ofIndex?_eq_some hfam, Nat.div_add_mod' (r / A) Λ.MAXI,
        Nat.add_zero, Nat.add_assoc, Nat.div_add_mod' r A]
      omega
    rw [hv'] at h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  next => simp at h

/-- Every defining gate of a constraint is the defining gate of its output. -/
private theorem dfnOf_of_mem (hD : D.Fits Λ) {fam : Family} {inst : ℕ} (hinst : inst < Λ.count fam)
    {g : Gate} (hg : g ∈ Λ.famDefs D x fam inst) : Λ.dfnOf D x g.out = some g := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
  have hlen := Λ.length_famDefs_le D x hD fam inst
  have hM := Λ.count_le_MAXI fam
  have hout := (Λ.defining_famDefs D x hD hinst i hi).2.1
  rw [hout]
  have hr : Λ.vAux D.pairs.length fam inst 0 + i - Λ.AUX =
      (fam.index * Λ.MAXI + inst) * Λ.A D.pairs.length + i := by
    unfold vAux
    omega
  set A := Λ.A D.pairs.length
  have hiA : i < A := by omega
  have h1 := Nat.mul_add_div_mod_of_lt (fam.index * Λ.MAXI + inst) hiA
  have h2 := Nat.mul_add_div_mod_of_lt fam.index (show inst < Λ.MAXI by omega)
  unfold dfnOf
  rw [ite_eq_left (by unfold vAux; omega), hr, h1.1, h1.2, h2.1, h2.2, Family.ofIndex?_index]
  simp only [hinst, ↓reduceIte, List.getElem?_eq_getElem hi]

end Layout

section Machine

variable {k : ℕ} {State : Type} [Fintype State] {ntm : MultiTapeNTM k Bool State} {κ : ℕ}
  {x : List Bool}

local notation "Λ" => layoutOf k State κ x.length
local notation "D" => machineData ntm

namespace Layout

/-- **A valid sequence of records gives a satisfying assignment.** -/
theorem exists_sat_of_valid {R : ℕ → StepRecord k State}
    (hR : StepRecord.Valid ntm x (layoutOf k State κ x.length).N R) :
    ∃ σ : ℕ → Bool, (Λ).Sat D x σ := by
  have hD := machineData_fits ntm κ x.length
  obtain ⟨σ, hσ1, hσ2⟩ := exists_extension ((Λ).σ₀ x R) ((Λ).dfnOf D x) id
    fun v g h => (Λ).dfnOf_spec D x hD h
  have hσ : ∀ v < (Λ).AUX, σ v = (Λ).σ₀ x R v := fun v hv => hσ1 v ((Λ).dfnOf_eq_none D x hv)
  refine ⟨σ, fun fam inst hinst g hg => ?_⟩
  have hdefs : ∀ g ∈ (Λ).famDefs D x fam inst, g.Holds σ := fun g hg =>
    hσ2 _ g ((Λ).dfnOf_of_mem D x hD hinst hg)
  rcases List.mem_append.1 hg with hg | hg
  · exact hdefs g hg
  · exact ((Λ).forall_famCons_iff D x σ fam inst hdefs fun _ => ⟨σ_vTT hσ, σ_vFF hσ⟩).2
      (meaning_of_valid hR hσ hinst) g hg

/-- **An accepting machine running within fewer than `N` steps has a satisfiable formula.** -/
theorem exists_sat_of_accepts {T : ℕ} (hT : ntm.RunsInTime x T) (hTN : T < (Λ).N)
    (hacc : ntm.Accepts x) : ∃ σ : ℕ → Bool, (Λ).Sat D x σ := by
  obtain ⟨R, hR⟩ := StepRecord.exists_valid_of_accepts hT hTN hacc
  exact exists_sat_of_valid hR

/-- **The quasilinear formula is satisfiable exactly when the machine accepts**, for a machine
running within fewer than `N` steps. -/
theorem sat_iff_accepts {T : ℕ} (hT : ntm.RunsInTime x T) (hTN : T < (Λ).N) :
    (∃ σ : ℕ → Bool, (Λ).Sat D x σ) ↔ ntm.Accepts x :=
  ⟨fun ⟨_, h⟩ => accepts_of_sat h, exists_sat_of_accepts hT hTN⟩

end Layout

end Machine

end Cslib.Complexity.CookLevin.Quasilinear
