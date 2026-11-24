/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.LocalTerm

/-!
# The interval count as a term

`condT` tests the numeric interval condition on a packed configuration, from
the end data of the interval given as terms (state and track codes, offsets
`offO`, movement codes `dC` with `sgnCode`, and window cells `cellO`).
`intervalCountT` sums the test over the replays of all `2^b` coin strings.

`intervalCountT_denote`: the term computes Complexitylib's
`localIntervalCount`, the tensor entry of an interval.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.LocalSim

open ProgTerm ProgTerm.Term Cslib.Turing _root_.Turing _root_.Turing.MultiTapePTM
  _root_.Turing.MultiTapeNTM.ChoiceTable

variable {w : List Bool}

/-! ### Reading a window cell -/

/-- The code of window cell `c` of a tape whose head has index `rho`. -/
def readN (t : NTape) (c rho : ℕ) : ℕ :=
  if c = rho then t.1 else if rho < c then t.2.2 / 3 ^ (c - rho - 1) % 3
  else t.2.1 / 3 ^ (rho - c - 1) % 3

theorem NTape.read_sub (t : NTape) (c rho : ℕ) : t.read ((c : ℤ) - rho) = readN t c rho := by
  unfold readN
  by_cases h0 : c = rho
  · subst h0; simp [NTape.read]
  by_cases h1 : rho < c
  · have : (c : ℤ) - rho = Int.ofNat (c - rho - 1 + 1) := by
      simp only [Int.ofNat_eq_natCast]; omega
    rw [this, ite_eq_right h0, ite_eq_left h1]; rfl
  · have : (c : ℤ) - rho = Int.negSucc (rho - c - 1) := by
      rw [Int.negSucc_eq]; omega
    rw [this, ite_eq_right h0, ite_eq_right h1]; rfl

theorem sign_cast (d : SignType) : ((d : ℤ)) = (sgnCode d : ℤ) - 1 := by
  cases d <;> rfl

/-! ### The numeric condition on packed configurations -/

/-- The interval condition read from the digits of a packed configuration. -/
def condN (k b Jp Jm stO trO : ℕ) (OffO DC CellO : ℕ → ℕ) (R a : ℕ) : Prop :=
  digN R a 0 = stO ∧ digN R a 2 = trO ∧
    (OffO 0 < b ∧ digN R a 1 + b * Jm + b = 1 + b * Jp + b * DC 0 + OffO 0) ∧
    (∀ h < k, OffO (h + 1) < b ∧ digN R a (3 + 4 * h + 3) = b * DC (h + 1) + OffO (h + 1)) ∧
    ∀ h < k, ∀ c < 3 * b, CellO (h * (3 * b) + c) =
      readN (digN R a (3 + 4 * h), digN R a (3 + 4 * h + 1), digN R a (3 + 4 * h + 2)) c
        (digN R a (3 + 4 * h + 3))

variable {k s : ℕ} {State : Type} {e : State ≃ Fin s}

theorem condN_iff {R : ℕ} (hR : 0 < R) {n : NCfg k} (hf : Fits R n) (b : ℕ)
    (J : Option (Fin k) → ℤ) (δ : Option (Fin k) → SignType) (cOut : ControlData k State)
    (wOut : Fin k → List (Option Bool)) (Jp Jm : ℕ) (OffO DC CellO : ℕ → ℕ)
    (hJ : J none = (Jp : ℤ) - Jm) (hdc0 : DC 0 = sgnCode (δ none))
    (hdc : ∀ h : Fin k, DC (h + 1) = sgnCode (δ (some h))) (hoff0 : OffO 0 = cOut.2.1 none)
    (hoff : ∀ h : Fin k, OffO (h + 1) = cOut.2.1 (some h)) (hlen : ∀ h, (wOut h).length = 3 * b)
    (hcell : ∀ (h : Fin k) c, c < 3 * b → CellO (h * (3 * b) + c) = cc ((wOut h).getD c none)) :
    condN k b Jp Jm (stc e cOut.1) (trc cOut.2.2) OffO DC CellO R (cpack R n) ↔
      NCond e b J δ cOut wOut n := by
  have dg : ∀ j, j < width k → digN R (cpack R n) j = comp n j := fun j hj =>
    digit_cpack hR hf hj
  have w3 : ∀ h : Fin k, 3 + 4 * (h : ℕ) + 3 < width k := fun h => by
    have := h.isLt; unfold width; omega
  have dtape : ∀ h : Fin k, ((digN R (cpack R n) (3 + 4 * h), digN R (cpack R n) (3 + 4 * h + 1),
      digN R (cpack R n) (3 + 4 * h + 2)) : NTape) = n.tapes h := fun h => by
    rw [dg _ (by have := w3 h; omega), dg _ (by have := w3 h; omega),
      dg _ (by have := w3 h; omega)]
    have a0 := comp_tape n h 0 (by norm_num)
    have a1 := comp_tape n h 1 (by norm_num)
    have a2 := comp_tape n h 2 (by norm_num)
    simp only [Nat.add_zero] at a0
    rw [a0, a1, a2]; rfl
  have drho : ∀ h : Fin k, digN R (cpack R n) (3 + 4 * h + 3) = n.rho h := fun h => by
    rw [dg _ (w3 h), comp_tape n h 3 (by norm_num)]; rfl
  have d0 : digN R (cpack R n) 0 = n.st := by rw [dg 0 (by unfold width; omega)]; rfl
  have d1 : digN R (cpack R n) 1 = n.ip := by rw [dg 1 (by unfold width; omega)]; rfl
  have d2 : digN R (cpack R n) 2 = n.tr := by rw [dg 2 (by unfold width; omega)]; rfl
  unfold condN NCond
  rw [d0, d1, d2, hoff0, hdc0]
  have hin : (n.ip + b * Jm + b = 1 + b * Jp + b * sgnCode (δ none) + cOut.2.1 none) ↔
      ((n.ip : ℤ) - 1 = b * (J none + δ none) + cOut.2.1 none) := by
    rw [hJ, sign_cast]
    constructor
    · intro h; have := congrArg (fun x : ℕ => (x : ℤ)) h; push_cast at this; linarith
    · intro h; have : ((n.ip + b * Jm + b : ℕ) : ℤ) =
        ((1 + b * Jp + b * sgnCode (δ none) + cOut.2.1 none : ℕ) : ℤ) := by push_cast; linarith
      exact_mod_cast this
  have hrho : ∀ h : Fin k, (n.rho h = b * sgnCode (δ (some h)) + cOut.2.1 (some h)) ↔
      ((n.rho h : ℤ) = b * (1 + δ (some h)) + cOut.2.1 (some h)) := fun h => by
    rw [sign_cast]
    constructor
    · intro hh; rw [hh]; push_cast; ring
    · intro hh; have : ((n.rho h : ℕ) : ℤ) =
        ((b * sgnCode (δ (some h)) + cOut.2.1 (some h) : ℕ) : ℤ) := by push_cast; linarith
      exact_mod_cast this
  constructor
  · rintro ⟨hs, ht, ⟨hi1, hi2⟩, hh, hw⟩
    refine ⟨hs, ht, ⟨hi1, hin.mp hi2⟩, fun h => ?_, fun h => ⟨hlen h, fun c hc => ?_⟩⟩
    · obtain ⟨a, b'⟩ := hh h h.isLt
      rw [hoff, hdc, drho] at *
      exact ⟨a, (hrho h).mp b'⟩
    · have := hw h h.isLt c hc
      rw [hcell h c hc, dtape, drho] at this
      rw [this, NTape.read_sub]
  · rintro ⟨hs, ht, ⟨hi1, hi2⟩, hh, hw⟩
    refine ⟨hs, ht, ⟨hi1, hin.mpr hi2⟩, fun h hk => ?_, fun h hk c hc => ?_⟩
    · have := hh ⟨h, hk⟩
      rw [hoff ⟨h, hk⟩, hdc ⟨h, hk⟩, show 3 + 4 * h + 3 = 3 + 4 *
          ((⟨h, hk⟩ : Fin k) : ℕ) + 3 from rfl,
        drho]
      exact ⟨this.1, (hrho ⟨h, hk⟩).mpr this.2⟩
    · have := (hw ⟨h, hk⟩).2 c hc
      rw [show h * (3 * b) + c = ((⟨h, hk⟩ : Fin k) : ℕ) * (3 * b) + c from rfl,
        hcell ⟨h, hk⟩ c hc, this,
        show 3 + 4 * h = 3 + 4 * ((⟨h, hk⟩ : Fin k) : ℕ) from rfl, dtape, drho, NTape.read_sub]

end Cslib.Complexity.NtimeDspace.LocalSim
