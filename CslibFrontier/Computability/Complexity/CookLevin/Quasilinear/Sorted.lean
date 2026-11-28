/-
Copyright (c) 2026 Samuel Schlesinger, Olivia Daniels. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Olivia Daniels
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.CookLevin.Quasilinear.RecordRun
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Tape contents from records sorted by position

List the times `t < N` of a run in the order of the keys `t + M * p t`, where `p t` is a number
standing for the position of a work head at time `t` and `N ≤ M`. In this order the visits of each
cell are consecutive and in time order, so the latest earlier visit of the cell visited at time `t`
is the time just before `t` in the sorted order, when it visits the same cell, and there is none
otherwise (`Cslib.Complexity.CookLevin.Quasilinear.StepRecord.tapeAt_of_sorted`). A formula can
therefore check every symbol read against a single neighbour once it has sorted the records.

## Main results

* `Cslib.Complexity.CookLevin.Quasilinear.StepRecord.tapeAt_of_sorted`: the contents of the cell
  read at time `t`, from the sorted order.
-/

public section

namespace Cslib.Complexity.CookLevin.Quasilinear

namespace StepRecord

variable {k : ℕ} {State : Type}

/-- Keys `a + M * p < b + M * q` with `a, b < M` order `p` and, on ties, `a`. -/
theorem lt_of_key_lt {M a b p q : ℕ} (_ha : a < M) (hb : b < M) (h : a + M * p < b + M * q) :
    p ≤ q ∧ (p = q → a < b) := by
  refine ⟨?_, fun hpq => by subst hpq; omega⟩
  by_contra hqp
  have h1 : M * (q + 1) ≤ M * p := Nat.mul_le_mul_left M (by omega)
  rw [Nat.mul_succ] at h1
  omega

/-- Keys that increase between consecutive positions of a permutation increase along it. -/
private theorem strictMono_key {N : ℕ} (π : Equiv.Perm (Fin N)) (key : ℕ → ℕ)
    (hkey : ∀ u (hu : u < N), 0 < u → key (π ⟨u - 1, by omega⟩) < key (π ⟨u, hu⟩)) :
    StrictMono fun u : Fin N => key (π u) := by
  cases N with
  | zero => exact fun a => a.elim0
  | succ n =>
    rw [Fin.strictMono_iff_lt_succ]
    intro i
    exact hkey (i + 1) (by omega) (by omega)

/-- **The contents of the cell read at time `t`, from the order of the keys `t + M * p t`.** The
latest earlier visit of the cell is the time just before `t` in the sorted order, when it visits
the same cell; otherwise no earlier time visits it. -/
theorem tapeAt_of_sorted (R : ℕ → StepRecord k State) (j : Fin k) {N M : ℕ} (hNM : N ≤ M)
    (π : Equiv.Perm (Fin N)) (p : ℕ → ℕ)
    (hp : ∀ s < N, ∀ t < N, (R s).pos j = (R t).pos j ↔ p s = p t)
    (hkey : ∀ u (hu : u < N), 0 < u →
      (π ⟨u - 1, by omega⟩ : ℕ) + M * p (π ⟨u - 1, by omega⟩) < π ⟨u, hu⟩ + M * p (π ⟨u, hu⟩))
    (t : Fin N) :
    tapeAt R j t ((R t).pos j) =
      if h : 0 < (π.symm t : ℕ) ∧ p (π ⟨π.symm t - 1, by omega⟩) = p t then
        (R (π ⟨π.symm t - 1, by omega⟩)).cellAfter j
      else none := by
  set key : ℕ → ℕ := fun s => s + M * p s with hk
  have hkey' : ∀ u (hu : u < N), 0 < u → key (π ⟨u - 1, by omega⟩) < key (π ⟨u, hu⟩) :=
    fun u hu h0 => hkey u hu h0
  have hmono := strictMono_key π key hkey'
  set u : ℕ := (π.symm t : ℕ) with hu
  have huN : u < N := (π.symm t).isLt
  have hπu : π ⟨u, huN⟩ = t := by simp [hu]
  -- another time visiting the same cell is before `t` exactly when it is sorted before `t`
  have hbefore : ∀ s : Fin N, p s = p t → (s : ℕ) < t → ((π.symm s : ℕ) < u) := by
    intro s hps hst
    by_contra hge
    rcases Nat.lt_or_ge u (π.symm s) with hlt | hle
    · have := hmono (show (⟨u, huN⟩ : Fin N) < π.symm s from hlt)
      beta_reduce at this
      rw [hπu] at this
      simp only [Equiv.apply_symm_apply, hk] at this
      rw [hps] at this
      omega
    · have : π.symm s = π.symm t := Fin.ext (by omega)
      have := π.symm.injective this
      rw [this] at hst
      omega
  split_ifs with h
  · obtain ⟨h0, hpp⟩ := h
    set t' := π ⟨u - 1, by omega⟩ with ht'
    have hkt := hkey' u huN h0
    rw [hπu] at hkt
    have hlt : (t' : ℕ) < t :=
      (lt_of_key_lt (M := M) (lt_of_lt_of_le t'.isLt hNM) (lt_of_lt_of_le t.isLt hNM) hkt).2 hpp
    refine tapeAt_eq_of_latest hlt ((hp _ t'.isLt _ t.isLt).2 hpp) fun s hs1 hs2 hsame => ?_
    have hsN : s < N := by omega
    have hps : p s = p t := (hp _ hsN _ t.isLt).1 hsame
    have hv := hbefore ⟨s, hsN⟩ hps hs2
    -- `s` is sorted before `t`, hence at or before the predecessor
    rcases Nat.lt_or_ge (π.symm ⟨s, hsN⟩) (u - 1) with hv' | hv'
    · have := hmono (show π.symm ⟨s, hsN⟩ < (⟨u - 1, by omega⟩ : Fin N) from hv')
      simp only [Equiv.apply_symm_apply, hk] at this
      rw [← ht', hps, ← hpp] at this
      omega
    · have : π.symm ⟨s, hsN⟩ = ⟨u - 1, by omega⟩ :=
        Fin.ext (by simp only; omega)
      have hs' : (⟨s, hsN⟩ : Fin N) = t' := by rw [ht', ← this]; simp
      have := congrArg Fin.val hs'
      simp only at this
      omega
  · refine tapeAt_eq_none fun s hs hsame => ?_
    have hsN : s < N := lt_trans hs t.isLt
    have hps : p s = p t := (hp _ hsN _ t.isLt).1 hsame
    have hv := hbefore ⟨s, hsN⟩ hps hs
    have h0 : 0 < u := by omega
    have hpp : p (π ⟨u - 1, by omega⟩) ≠ p t := fun e => h ⟨h0, e⟩
    set t'' := π ⟨u - 1, by omega⟩ with ht''
    have hkt := hkey' u huN h0
    rw [hπu] at hkt
    have hle : key s ≤ key t'' := by
      rcases Nat.lt_or_ge (π.symm ⟨s, hsN⟩) (u - 1) with hv' | hv'
      · have := hmono (show π.symm ⟨s, hsN⟩ < (⟨u - 1, by omega⟩ : Fin N) from hv')
        simp only [Equiv.apply_symm_apply] at this
        exact this.le
      · have : π.symm ⟨s, hsN⟩ = ⟨u - 1, by omega⟩ :=
        Fin.ext (by simp only; omega)
        have hs' : (⟨s, hsN⟩ : Fin N) = t'' := by rw [ht'', ← this]; simp
        rw [← hs']
    have hsM : s < M := by omega
    have h1 : p s ≤ p t'' := by
      rcases Nat.lt_or_ge (key s) (key t'') with hlt | heq
      · exact (lt_of_key_lt hsM (lt_of_lt_of_le t''.isLt hNM) hlt).1
      · have he : key s = key t'' := le_antisymm hle heq
        by_contra hc
        have h1 : M * (p t'' + 1) ≤ M * p s := Nat.mul_le_mul_left M (by omega)
        rw [Nat.mul_succ] at h1
        simp only [hk] at he
        have := t''.isLt
        omega
    have h2 := (lt_of_key_lt (lt_of_lt_of_le t''.isLt hNM) (lt_of_lt_of_le t.isLt hNM) hkt).1
    rw [hps] at h1
    exact hpp (le_antisymm h2 h1)

end StepRecord

end Cslib.Complexity.CookLevin.Quasilinear
