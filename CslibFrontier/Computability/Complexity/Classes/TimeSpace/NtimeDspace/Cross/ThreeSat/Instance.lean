/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.PrimeBoundExact
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.ThreeSat.Decode
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Polylog
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Bitwise

/-!
# Instances of #3-SAT bit queries and the prime window

An instance of Corollary 7.2 is a 3-CNF formula `φ` on `n` variables with `m ≥ 2` clauses in
which every variable occurs, together with a bit position `j` (as in the paper, before Theorem 2.3:
an integer is computed when each of its bits is computed from its position). It is written as the
framed binary digits of `j` followed by the slot encoding `encSlots φ` (`encInstance`); the encoding
is injective (`encInstance_injective`) and carries no information about satisfiability.

`prime_window` is the size condition on the primes of the residue form of Theorem 2.3 used for the
Chinese remainder step: for every `c`, once `s` is large, the primes `p` with
`(2 (log₂ s + 1))^c < p ≤ s` have product above `2^(s/2 + 1)` (from the prime product bound
`prime_prod_lower_bound_nat`).
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Cross.ThreeSat

open Finset NtimeDspace.Cross.TermBlocks Cslib.Logic.PL _root_.Turing.MultiTapeTM

/-! ### Instances -/

/-- An instance of Corollary 7.2: a 3-CNF formula with at least two clauses in which every
variable occurs, and a bit position `j`. -/
structure Instance where
  /-- The number of variables. -/
  n : ℕ
  /-- The formula. -/
  φ : CNF (Fin n)
  /-- The bit position. -/
  j : ℕ
  three : ∀ C ∈ φ, C.length ≤ 3
  occurs : EveryVarOccurs φ
  two_le : 2 ≤ φ.length

/-- The encoding of an instance: the framed digits of `j`, then `encSlots φ`. -/
def encInstance (a : Instance) : List Bool := frame (encNat a.j) ++ encSlots a.φ

theorem length_le_length_enc {n : ℕ} (φ : CNF (Fin n)) : φ.length ≤ (encSlots φ).length := by
  rw [length_enc]; nlinarith

theorem slot_injective {n : ℕ} {o o' : Option (Literal (Fin n))}
    (h : slot o = slot o') : o = o' := by
  rcases o with _ | ⟨i, b⟩ <;> rcases o' with _ | ⟨i', b'⟩
  · rfl
  · simp only [slot] at h; omega
  · simp only [slot] at h; omega
  · simp only [slot] at h
    have h1 := Bool.toNat_le b; have h2 := Bool.toNat_le b'
    have hi : (i : ℕ) = i' := by omega
    have hb : b.toNat = b'.toNat := by omega
    have hb' : b = b' := by cases b <;> cases b' <;> simp_all
    rw [Fin.ext hi, hb']

/-- The encoding of a 3-CNF formula determines it. -/
theorem enc_inj {x : List Bool} {n n' : ℕ} {φ : CNF (Fin n)} {φ' : CNF (Fin n')}
    (h3 : ∀ C ∈ φ, C.length ≤ 3) (h3' : ∀ C ∈ φ', C.length ≤ 3)
    (h : frame x ++ encSlots φ = frame x ++ encSlots φ') : n = n' ∧ HEq φ φ' := by
  set s := (frame x ++ encSlots φ).length
  have hw : (frame x ++ encSlots φ).length ≤ bnd s := by
    unfold bnd; nlinarith
  have hw' : (frame x ++ encSlots φ').length ≤ bnd s := by rw [← h]; exact hw
  have hm : φ.length ≤ s := (length_le_length_enc φ).trans (by simp [s])
  have hm' : φ'.length ≤ s := (length_le_length_enc φ').trans
      (by rw [show s = _ from congrArg List.length h]; simp)
  have hn : n = n' := by rw [← nW_eq (φ := φ) hw, ← nW_eq (φ := φ') hw', h]
  subst hn
  refine ⟨rfl, heq_of_eq ?_⟩
  have hlen : φ.length = φ'.length := by rw [← mW_eq hw hm, ← mW_eq hw' hm', h]
  refine List.ext_getElem hlen fun c hc hc' => ?_
  refine List.ext_getElem? fun j => ?_
  rcases Nat.lt_or_ge j 3 with hj | hj
  · have e1 := svW_eq hw hc hj
    have e2 := svW_eq hw' hc' hj
    rw [h] at e1
    exact slot_injective (e1.symm.trans e2)
  · rw [List.getElem?_eq_none ((h3 _ (List.getElem_mem _)).trans hj),
      List.getElem?_eq_none ((h3' _ (List.getElem_mem _)).trans hj)]

theorem encInstance_injective : Function.Injective encInstance := by
  rintro ⟨n, φ, j, h3, ho, h2⟩ ⟨n', φ', j', h3', ho', h2'⟩ h
  simp only [encInstance] at h
  obtain ⟨hj, he⟩ := frame_append_inj h
  have hj' : j = j' := encNat.injective hj
  subst hj'
  obtain ⟨rfl, hφ⟩ := enc_inj h3 h3' (congrArg (frame (encNat j) ++ ·) he)
  cases eq_of_heq hφ
  rfl

/-- The encoding of instances, as an embedding. -/
def instEnc : Instance ↪ List Bool := ⟨encInstance, encInstance_injective⟩

/-! ### Reading the bit position -/

theorem ib_frame_odd {x y : List Bool} {k : ℕ} (hk : k < x.length) :
    ib (frame x ++ y) (2 * k + 1) = (x[k]).toNat := by
  rw [ib_some]
  rw [List.getElem?_append_left (by simp; omega), getElem?_frame_lt (by omega),
      ite_eq_right (by omega)]
  congr 2
  omega

theorem bitsNum_frame_encNat (j : ℕ) (y : List Bool) :
    bitsNum (encNat j).length (fun k => ib (frame (encNat j) ++ y) (2 * k + 1)) = j := by
  have hlt : j < 2 ^ (encNat j).length := by
    rw [encNat_apply, Nat.size_eq_bits_len]; exact Nat.lt_size_self j
  conv_rhs => rw [← bitsNum_digits hlt]
  refine bitsNum_congr fun k hk => ?_
  rw [ib_frame_odd hk, ← Nat.toNat_testBit, Nat.testBit_eq_inth]
  simp only [encNat_apply] at hk ⊢
  rw [List.getI_eq_getElem _ hk]

/-! ### The prime window -/

theorem prod_window_mono {H X X' : ℕ} (h : X ≤ X') :
    ∏ p ∈ primesWindow H X, p ≤ ∏ p ∈ (Ioc H X').filter Nat.Prime, p := by
  refine prod_le_prod_of_subset_of_one_le ?_ fun p hp _ => ?_
  · intro p hp
    simp only [primesWindow, mem_filter, mem_Ioc] at hp ⊢
    exact ⟨⟨hp.1.1, hp.1.2.trans h⟩, hp.2⟩
  · simp only [mem_filter] at hp
    exact hp.2.one_lt.le

/-- **The prime window of the residue form of Theorem 2.3 is large enough for the Chinese remainder
step.** For every `c`, once `s` is large, the primes in `((2 (log₂ s + 1))^c, s]` have product above
`2^(s/2 + 1)`. -/
theorem prime_window (c : ℕ) : ∃ s₁, ∀ s, s₁ ≤ s →
    2 ^ (s / 2 + 1) < ∏ p ∈ (Ioc ((2 * (Nat.log 2 s + 1)) ^ c) s).filter Nat.Prime, p := by
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp
    ((Polylog.eventually_polylog_le 8 2).and ((Polylog.eventually_polylog_le 32 (2 * c + 1)).and
      (Filter.eventually_ge_atTop 64)))
  refine ⟨N₁ + 2, fun s hs => ?_⟩
  set X := 2 * (s / 2)
  have hXs : X ≤ s := by omega
  have hsX : s ≤ X + 1 := by omega
  obtain ⟨h8, h32, h64⟩ := hN₁ X (by omega)
  set L := X.log2 + 1
  set H := (2 * (Nat.log 2 s + 1)) ^ c
  have hH2 : 2 ≤ H ∨ H < 2 := le_or_gt 2 H
  -- the logarithms
  have hXL : X < 2 ^ L := Nat.lt_log2_self
  have hlogs : Nat.log 2 s + 1 ≤ 2 * L := by
    have h1 : Nat.log 2 s ≤ Nat.log 2 (2 * X) := Nat.log_mono_right (by omega)
    have h2X : Nat.log 2 (2 * X) = Nat.log 2 X + 1 := by
      rw [mul_comm, Nat.log_mul_base (by norm_num) (by omega)]
    change Nat.log 2 s + 1 ≤ 2 * (X.log2 + 1)
    rw [Nat.log2_eq_log_two]
    omega
  have hL1 : 1 ≤ L := by omega
  -- the three factors
  have hsq : 8 * L ≤ Nat.sqrt X := Nat.le_sqrt.mpr (by nlinarith)
  have hsqX : Nat.sqrt X * Nat.sqrt X ≤ X := Nat.sqrt_le X
  have hHH : H * H ≤ X / 8 := by
    have e0 : H * H = (2 * (Nat.log 2 s + 1)) ^ (2 * c) := by
      simp only [H]; rw [← pow_add]; ring_nf
    have e1 : H * H ≤ (4 * L) ^ (2 * c) := by
      rw [e0]; exact Nat.pow_le_pow_left (by omega) _
    have e2 : 8 * (4 * L) ^ (2 * c) ≤ (32 * L) ^ (2 * c + 1) := by
      calc 8 * (4 * L) ^ (2 * c) ≤ (32 * L) * (32 * L) ^ (2 * c) :=
            Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left (by omega) _)
        _ = (32 * L) ^ (2 * c + 1) := by rw [pow_succ, mul_comm]
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    nlinarith
  have hH_le : H ≤ 2 ^ H := Nat.lt_two_pow_self.le
  have f1 : X + 1 ≤ 2 ^ L := hXL
  have f2 : X ^ Nat.sqrt X ≤ 2 ^ (L * Nat.sqrt X) := by
    rw [pow_mul]; exact Nat.pow_le_pow_left hXL.le _
  have f3 : H ^ H ≤ 2 ^ (H * H) := by
    rw [pow_mul]; exact Nat.pow_le_pow_left hH_le _
  have hexp : L + L * Nat.sqrt X + H * H + (s / 2 + 1) < X := by
    have : L * Nat.sqrt X ≤ X / 8 := by
      rw [Nat.le_div_iff_mul_le (by norm_num)]; nlinarith
    have : L ≤ X / 8 := by
      rw [Nat.le_div_iff_mul_le (by norm_num)]; nlinarith
    omega
  -- the prime product bound
  have hEven : Even X := ⟨s / 2, by omega⟩
  rcases hH2 with hH2 | hH2
  · have h43 := prime_prod_lower_bound_nat X H hEven (by omega) hH2
    have hmono := prod_window_mono (H := H) hXs
    have hpos : 0 < (X + 1) * X ^ Nat.sqrt X * H ^ H := by positivity
    have key : 2 ^ (s / 2 + 1) * ((X + 1) * X ^ Nat.sqrt X * H ^ H) < 2 ^ X := by
      calc 2 ^ (s / 2 + 1) * ((X + 1) * X ^ Nat.sqrt X * H ^ H)
          ≤ 2 ^ (s / 2 + 1) * (2 ^ L * 2 ^ (L * Nat.sqrt X) * 2 ^ (H * H)) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.mul_le_mul f1 f2) f3)
        _ = 2 ^ (L + L * Nat.sqrt X + H * H + (s / 2 + 1)) := by
            rw [← pow_add, ← pow_add, ← pow_add]; ring_nf
        _ < 2 ^ X := Nat.pow_lt_pow_right (by norm_num) hexp
    have : 2 ^ (s / 2 + 1) * ((X + 1) * X ^ Nat.sqrt X * H ^ H) <
        (∏ p ∈ primesWindow H X, p) * ((X + 1) * X ^ Nat.sqrt X * H ^ H) := by
      calc _ < 2 ^ X := key
        _ ≤ _ := by rw [mul_comm]; exact h43
    exact (Nat.lt_of_mul_lt_mul_right this).trans_le hmono
  · -- `H ≤ 1`: the prime product bound with `H = 2`, and the window only grows
    have h43 := prime_prod_lower_bound_nat X 2 hEven (by omega) le_rfl
    have hsub : ∏ p ∈ primesWindow 2 X, p ≤ ∏ p ∈ (Ioc H s).filter Nat.Prime, p := by
      refine prod_le_prod_of_subset_of_one_le ?_ fun p hp _ => ?_
      · intro p hp
        simp only [primesWindow, mem_filter, mem_Ioc] at hp ⊢
        exact ⟨⟨by omega, hp.1.2.trans hXs⟩, hp.2⟩
      · simp only [mem_filter] at hp
        exact hp.2.one_lt.le
    have key : 2 ^ (s / 2 + 1) * ((X + 1) * X ^ Nat.sqrt X * 2 ^ 2) < 2 ^ X := by
      calc 2 ^ (s / 2 + 1) * ((X + 1) * X ^ Nat.sqrt X * 2 ^ 2)
          ≤ 2 ^ (s / 2 + 1) * (2 ^ L * 2 ^ (L * Nat.sqrt X) * 2 ^ 2) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.mul_le_mul f1 f2) le_rfl)
        _ = 2 ^ (L + L * Nat.sqrt X + 2 + (s / 2 + 1)) := by
            rw [← pow_add, ← pow_add, ← pow_add]; ring_nf
        _ < 2 ^ X := Nat.pow_lt_pow_right (by norm_num) (by
            have : L * Nat.sqrt X ≤ X / 8 := by
              rw [Nat.le_div_iff_mul_le (by norm_num)]; nlinarith
            have : L ≤ X / 8 := by
              rw [Nat.le_div_iff_mul_le (by norm_num)]; nlinarith
            omega)
    have : 2 ^ (s / 2 + 1) * ((X + 1) * X ^ Nat.sqrt X * 2 ^ 2) <
        (∏ p ∈ primesWindow 2 X, p) * ((X + 1) * X ^ Nat.sqrt X * 2 ^ 2) := by
      calc _ < 2 ^ X := key
        _ ≤ _ := by rw [mul_comm]; exact h43
    exact (Nat.lt_of_mul_lt_mul_right this).trans_le hsub

end Cslib.Complexity.NtimeDspace.Cross.ThreeSat
