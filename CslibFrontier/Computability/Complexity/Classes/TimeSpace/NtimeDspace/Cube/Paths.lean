/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.PathsAux

/-!
# Index lengths (Lemma 6.3)

The parameters of §4.3 for a network of size `s`: `h_*` is the largest power of two with
`2^{3 h_*} ≤ s` (`hstar`), the first clique has `q_* = 2^{h_*}` nodes (`K = q_*/2` vertex groups),
choice fields have `3 ⌈log s⌉ + 5` bits, and the precision is arbitrary.

`formula_cost` is Lemma 6.3: for networks with `s^{O(1)}` vertices, `O(s)` edges and degree
`O(log s)` and every `ℓ` of order `log s`, the cost (the largest total index length on a
root-to-leaf path, plus `ℓ` per inner node) of the formula is `O(s / √(log s))`, written as `C · (s
/ ⌊√⌊log₂ s⌋⌋ + 1)`. The proof gives a
budget `bud` paying for every node (`AGen.Budgeted`): along the descent the choices take `o(F)`
bits, the last label `O(F)`, each table entry from a parent of name length `h` takes
`O(F √h 2^{-h/4})` bits, and the transport recursion `O(√W + log² W)`, with `F = s / √h_*`.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Cube

open Finset

/-- `h_*`: the largest power of two with `2^{3 h_*} ≤ s` (for `s ≥ 8`). -/
def hstar (s : ℕ) : ℕ := 2 ^ Nat.log 2 (Nat.log 2 s / 3)

/-- The setup of §4.3 for a network of size `s` and a precision `P`. -/
def setupOf (s : ℕ) {V : ℕ} (G : Cross.EdgeNet ℤ (Fin V)) (P : ℕ) : Setup where
  V := V
  G := G
  K := 2 ^ (hstar s - 1)
  fw := 3 * (Nat.log 2 s + 1) + 5
  P := P

/-- **Lemma 6.3.** For every constant `C₁` there are `C` and `s₀` such that for every `s ≥ s₀`,
every network with at most `(s+2)^C₁` vertices, at most `C₁ (s+1)` edges and degrees at most
`C₁ (log₂ s + 1)`, every precision, and every `ℓ ≤ C₁ (log₂ s + 1)`, the setup of size `s` is good
and the formula has cost at most `C · (s / ⌊√⌊log₂ s⌋⌋ + 1)` for every fuel. -/
theorem formula_cost (C₁ : ℕ) : ∃ C s₀ : ℕ, ∀ s, s₀ ≤ s → ∀ {V : ℕ}
    (G : Cross.EdgeNet ℤ (Fin V)) (P ℓ : ℕ),
    V ≤ (s + 2) ^ C₁ → G.M ≤ C₁ * (s + 1) → (∀ v, (G.ports v).length ≤ C₁ * (Nat.log 2 s + 1)) →
    ℓ ≤ C₁ * (Nat.log 2 s + 1) →
    (setupOf s G P).Good ∧
    ∀ n, ((setupOf s G P).gen.tree P n (.cl [])).cost ℓ ≤ C * (s / Nat.sqrt (Nat.log 2 s) + 1) := by
  refine ⟨(22 + 2 * C₁) + 588 * (4 * C₁ + 3) + 2 * C₁ * (3 * C₁ + 18) + 9600 * (4 * C₁ + 3) +
    16128 * (4 * C₁ + 3) + (5 + Nat.size (384 * (4 * C₁ + 3) ^ 2)) *
      (26 + 4 * Nat.size (384 * (4 * C₁ + 3) ^ 2) + 6 * C₁),
    2 ^ 192 + 48 * (4 * C₁ + 3) ^ 2 + C₁ + 1, ?_⟩
  intro s hs V G P ℓ hV hM hdeg hℓ
  generalize hcA : 4 * C₁ + 3 = cA at hs ⊢
  generalize hc' : Nat.size (384 * cA ^ 2) = c'
  have hs48 : 48 * cA ^ 2 + 1 ≤ s := by omega
  have hsC : C₁ ≤ s := by omega
  have hs192 : 2 ^ 192 ≤ s := by omega
  clear hs
  -- the parameters
  generalize hL : Nat.log 2 s = L at hdeg hℓ ⊢
  have hL192 : 192 ≤ L := hL ▸ Nat.le_log_of_pow_le (by norm_num) hs192
  have hsL : 2 ^ L ≤ s := hL ▸ Nat.pow_log_le_self 2 (by omega)
  have hsL' : s < 2 ^ (L + 1) := hL ▸ Nat.lt_pow_succ_log_self (by norm_num) s
  clear hs192
  generalize he : Nat.log 2 (L / 3) = e
  have he6 : 6 ≤ e := he ▸ Nat.le_log_of_pow_le (by norm_num) (by omega)
  have hh3 : 2 ^ e ≤ L / 3 := he ▸ Nat.pow_log_le_self 2 (by omega)
  have hh6 : L < 6 * 2 ^ e := by
    have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (L / 3)
    rw [he, pow_succ] at this
    omega
  have hhs : hstar s = 2 ^ e := by rw [hstar, hL, he]
  generalize hh : 2 ^ e = h at hh3 hh6 hhs
  have hh1 : 1 ≤ h := hh ▸ Nat.one_le_two_pow
  have heh : e ≤ h := hh ▸ (Nat.lt_two_pow_self).le
  have hLh : h ≤ L := by omega
  have hq3 : (2 ^ h) ^ 3 ≤ s := by
    rw [← pow_mul]; exact (Nat.pow_le_pow_right (by norm_num) (by omega)).trans hsL
  have hLq : L ^ 3 ≤ 2 ^ h := by
    calc L ^ 3 ≤ (6 * h) ^ 3 := Nat.pow_le_pow_left hh6.le 3
      _ = 216 * (2 ^ e) ^ 3 := by rw [hh]; ring
      _ ≤ 2 ^ 2 ^ e := two_pow_cube_le e he6
      _ = 2 ^ h := by rw [hh]
  generalize hq₀ : 2 ^ h = q₀ at hq3 hLq
  have hL1 : 1 ≤ L := by omega
  have hLq0 : L ≤ q₀ := (Nat.le_self_pow (by norm_num) L).trans hLq
  have hq1 : 1 ≤ q₀ := hq₀ ▸ Nat.one_le_two_pow
  have hq2s : q₀ ^ 2 ≤ s := (Nat.pow_le_pow_right hq1 (by norm_num)).trans hq3
  have hqs : q₀ ≤ s := (Nat.le_self_pow (by norm_num) q₀).trans hq2s
  have hL4 : L ^ 4 ≤ s := by
    calc L ^ 4 = L * L ^ 3 := by ring
      _ ≤ q₀ * q₀ := Nat.mul_le_mul hLq0 hLq
      _ = q₀ ^ 2 := by ring
      _ ≤ s := hq2s
  have hℓL : ℓ ≤ 2 * C₁ * L := by
    calc ℓ ≤ C₁ * (L + 1) := hℓ
      _ ≤ C₁ * (2 * L) := Nat.mul_le_mul_left _ (by omega)
      _ = 2 * C₁ * L := by ring
  -- the setup
  have hK : (setupOf s G P).K = 2 ^ (h - 1) := by rw [setupOf, hhs]
  have hK1 : 1 ≤ (setupOf s G P).K := hK ▸ Nat.one_le_two_pow
  have h2K : 2 * (setupOf s G P).K = 2 ^ 2 ^ e := by
    rw [hK, ← pow_succ', hh]; congr 1; omega
  have hKq : (setupOf s G P).K ≤ q₀ := by
    rw [hK, ← hq₀]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hq : (setupOf s G P).C₀.q = 2 ^ 2 ^ e := h2K
  have hfw : (setupOf s G P).fw = 3 * (L + 1) + 5 := by rw [setupOf, hL]
  have hΦ : (setupOf s G P).C₀.potential ≤ 64 * (cA * s) ^ 2 := by
    have hp : (setupOf s G P).C₀.potential ≤
        64 * (G.M + (setupOf s G P).K * (C₁ * (L + 1) + 1) + (setupOf s G P).K ^ 3) ^ 2 :=
      firstClique_potential G _ hK1 (C₁ * (L + 1)) hdeg
    refine hp.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ 2))
    have h1 : G.M ≤ 2 * C₁ * s :=
      calc G.M ≤ C₁ * (s + 1) := hM
        _ ≤ C₁ * (2 * s) := Nat.mul_le_mul_left _ (by omega)
        _ = 2 * C₁ * s := by ring
    have h2 : (setupOf s G P).K * (C₁ * (L + 1) + 1) ≤ (2 * C₁ + 1) * s := by
      have hc : C₁ * (L + 1) + 1 ≤ (2 * C₁ + 1) * L := by
        have := Nat.mul_le_mul_left C₁ hL1
        rw [Nat.mul_one] at this
        calc C₁ * (L + 1) + 1 = C₁ * L + C₁ + 1 := by ring
          _ ≤ C₁ * L + C₁ * L + L := by omega
          _ = (2 * C₁ + 1) * L := by ring
      calc (setupOf s G P).K * (C₁ * (L + 1) + 1) ≤ q₀ * ((2 * C₁ + 1) * L) :=
            Nat.mul_le_mul hKq hc
        _ = (2 * C₁ + 1) * (q₀ * L) := by ring
        _ ≤ (2 * C₁ + 1) * (q₀ * q₀) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hLq0)
        _ = (2 * C₁ + 1) * q₀ ^ 2 := by ring
        _ ≤ (2 * C₁ + 1) * s := Nat.mul_le_mul_left _ hq2s
    have h3 : (setupOf s G P).K ^ 3 ≤ s := (Nat.pow_le_pow_left hKq 3).trans hq3
    have : cA * s = 2 * C₁ * s + (2 * C₁ + 1) * s + s + s := by rw [← hcA]; ring
    omega
  have hnf : ∀ v, (setupOf s G P).nFac0 v ≤ 1 + V + G.M := fun v => by
    change 1 + (if v < (setupOf s G P).K then V else G.M) ≤ 1 + V + G.M
    split_ifs <;> omega
  generalize setupOf s G P = S at hK hK1 h2K hKq hq hfw hΦ hnf ⊢
  generalize hΦ₀ : S.C₀.potential = Φ₀ at hΦ
  -- Good
  refine ⟨⟨hK1, ⟨e, h2K⟩, ?_⟩, ?_⟩
  · show 12 * (S.C₀.potential + 1) < 2 ^ (S.fw - 1)
    rw [hΦ₀, hfw, show 3 * (L + 1) + 5 - 1 = 3 * (L + 1) + 4 by omega, pow_add, pow_mul']
    have hs3 : s ^ 3 < (2 ^ (L + 1)) ^ 3 := Nat.pow_lt_pow_left hsL' (by norm_num)
    have h16 : 16 * s ^ 2 * (48 * cA ^ 2 + 1) ≤ 16 * s ^ 2 * s := Nat.mul_le_mul_left _ hs48
    have hs2 : 1 ≤ s ^ 2 := Nat.one_le_pow _ _ (by omega)
    have : 12 * (Φ₀ + 1) ≤ 16 * s ^ 3 := by
      have : 12 * (Φ₀ + 1) ≤ 12 * (64 * (cA * s) ^ 2 + 1) := by omega
      calc 12 * (Φ₀ + 1) ≤ 12 * (64 * (cA * s) ^ 2 + 1) := this
        _ = 768 * cA ^ 2 * s ^ 2 + 12 := by ring
        _ ≤ 16 * s ^ 2 * (48 * cA ^ 2 + 1) := by nlinarith
        _ ≤ 16 * s ^ 2 * s := h16
        _ = 16 * s ^ 3 := by ring
    calc 12 * (Φ₀ + 1) ≤ 16 * s ^ 3 := this
      _ < 16 * (2 ^ (L + 1)) ^ 3 := by omega
      _ = (2 ^ (L + 1)) ^ 3 * 2 ^ 4 := by ring
  -- the cost
  intro n
  have hB := S.budgeted ⟨e, ℓ, codeWidth (Φ₀ / 2 ^ e), Nat.sqrt (230400 * Φ₀ / 2 ^ e),
      Nat.clog 2 (1 + V + G.M), Nat.clog 2 (nFac (2 ^ 2 ^ e)), 6 * (Φ₀ / 2 ^ e)⟩ hq
    (fun a ha => codeWidth_mono ((Nat.le_div_iff_mul_le (by positivity)).mpr (hΦ₀ ▸ ha)))
    (fun v hc => by rw [← hΦ₀]; exact S.xiWidth_le hq hc v)
    (fun v => (hnf v).trans (Nat.le_pow_clog (by norm_num) _))
    (fun k hk => (nFac_mono (Nat.pow_le_pow_right (by norm_num)
      (Nat.pow_le_pow_right (by norm_num) hk.le))).trans (Nat.le_pow_clog (by norm_num) _))
    (by rw [hΦ₀])
  have hcost := AGen.tree_cost_le S.gen hB P n (.cl []) trivial
  have hd := BudPar.desc_le ⟨e, ℓ, codeWidth (Φ₀ / 2 ^ e), Nat.sqrt (230400 * Φ₀ / 2 ^ e),
      Nat.clog 2 (1 + V + G.M), Nat.clog 2 (nFac (2 ^ 2 ^ e)), 6 * (Φ₀ / 2 ^ e)⟩ S.fw e le_rfl
  have ha := BudPar.asc_le ⟨e, ℓ, codeWidth (Φ₀ / 2 ^ e), Nat.sqrt (230400 * Φ₀ / 2 ^ e),
      Nat.clog 2 (1 + V + G.M), Nat.clog 2 (nFac (2 ^ 2 ^ e)), 6 * (Φ₀ / 2 ^ e)⟩ e le_rfl
  simp only [Nat.sub_self, pow_zero, Nat.div_one] at ha
  simp only [Setup.bud, List.length_nil, Nat.sub_zero] at hcost
  simp only [BudPar.desc] at hd
  generalize S.gen.tree P n (.cl []) = tr at hcost
  generalize hΛ : codeWidth (Φ₀ / 2 ^ e) = Λ at hd ha hcost
  generalize hΞ : Nat.sqrt (230400 * Φ₀ / 2 ^ e) = Ξ at hd ha hcost
  generalize hD0 : Nat.clog 2 (1 + V + G.M) = D0 at hd ha hcost
  generalize hDm : Nat.clog 2 (nFac (2 ^ 2 ^ e)) = Dm at hd ha hcost
  generalize hWm : 6 * (Φ₀ / 2 ^ e) = Wm at hd ha hcost
  set A := BudPar.asc ⟨e, ℓ, Λ, Ξ, D0, Dm, Wm⟩ e
  set D := BudPar.desc ⟨e, ℓ, Λ, Ξ, D0, Dm, Wm⟩ S.fw e
  have hcw : choiceWidth (2 ^ 2 ^ (e - 1)) S.fw = 2 * q₀ ^ 2 * S.fw := by
    have hg2 : (2 ^ 2 ^ (e - 1)) ^ 2 = q₀ := by
      rw [← pow_mul, ← hq₀, ← hh, ← pow_succ]; congr 2; omega
    change 2 * (2 ^ 2 ^ (e - 1)) ^ 4 * S.fw = _
    rw [show (2 ^ 2 ^ (e - 1)) ^ 4 = ((2 ^ 2 ^ (e - 1)) ^ 2) ^ 2 by ring, hg2]
  rw [hcw] at hd
  have htot : tr.cost ℓ ≤ e * (2 * q₀ ^ 2 * S.fw + ℓ) + Λ + 2 * ℓ +
      (ℓ * (1 + D0) + trB ℓ Wm + e * (ℓ * (1 + Dm)) + Ξ) := by
    omega
  -- the parts
  generalize hR : L.sqrt = R
  have hR2 : R ^ 2 ≤ L := hR ▸ Nat.sqrt_le' L
  have hR1 : 1 ≤ R := hR ▸ Nat.le_sqrt'.mpr (by omega)
  have hRL : R ≤ L := (Nat.le_self_pow (by norm_num) R).trans hR2
  have hfw' : S.fw ≤ 11 * L := by omega
  have heL : e ≤ L := by omega
  have hXh : ∀ Y, Y / 2 ^ e * L ≤ 6 * Y := fun Y =>
    calc Y / 2 ^ e * L ≤ Y / 2 ^ e * (6 * 2 ^ e) := Nat.mul_le_mul_left _ (by omega)
      _ = 6 * (Y / 2 ^ e * 2 ^ e) := by ring
      _ ≤ 6 * Y := Nat.mul_le_mul_left _ (Nat.div_mul_le_self _ _)
  have T1 := part_desc heL hRL hfw' hℓL hLq hq3 hqs
  have T2 : Λ * R ≤ 588 * cA * s :=
    part_sqrt (c := 900) (hΛ ▸ codeWidth_sq_le _) hR2 (hXh Φ₀) hΦ (by norm_num)
  have hΦ' : 230400 * Φ₀ ≤ 64 * (480 * cA * s) ^ 2 :=
    calc 230400 * Φ₀ ≤ 230400 * (64 * (cA * s) ^ 2) := Nat.mul_le_mul_left _ hΦ
      _ = 64 * (480 * cA * s) ^ 2 := by ring
  have hΞ2 : Ξ ^ 2 ≤ 1 * (230400 * Φ₀ / 2 ^ e) := by
    rw [one_mul, ← hΞ]; exact Nat.sqrt_le' _
  have h384 : (1 : ℕ) * 384 ≤ 20 ^ 2 := by norm_num
  have T4 : Ξ * R ≤ 20 * (480 * cA) * s :=
    part_sqrt hΞ2 hR2 (hXh (230400 * Φ₀)) hΦ' h384
  have hD0' : D0 ≤ (3 * C₁ + 8) * L := hD0 ▸ clog_D0 hsL' hL1 hsC hV hM
  have hDm' : Dm ≤ 6 * L := hDm ▸ clog_Dm hh hq₀ hq1 hLh
  have T3 := part_prod hℓL hD0' hDm' heL hRL hL1 hL4
  have hWR : Wm * R ^ 2 ≤ (48 * cA * s) ^ 2 := by
    rw [← hWm]
    calc 6 * (Φ₀ / 2 ^ e) * R ^ 2 ≤ 6 * (Φ₀ / 2 ^ e * L) := by
          rw [mul_assoc]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hR2)
      _ ≤ 6 * (6 * (64 * (cA * s) ^ 2)) :=
          Nat.mul_le_mul_left _ ((hXh Φ₀).trans (Nat.mul_le_mul_left _ hΦ))
      _ = (48 * cA * s) ^ 2 := by ring
  have hW6 : Wm ≤ 384 * cA ^ 2 * s ^ 2 := by
    rw [← hWm]
    calc 6 * (Φ₀ / 2 ^ e) ≤ 6 * Φ₀ := Nat.mul_le_mul_left _ (Nat.div_le_self _ _)
      _ ≤ 6 * (64 * (cA * s) ^ 2) := Nat.mul_le_mul_left _ hΦ
      _ = 384 * cA ^ 2 * s ^ 2 := by ring
  have hsz : Nat.size Wm ≤ (4 + c') * L := hc' ▸ size_Wm hW6 hsL' hL1
  have T5 := part_tr hWR hsz hℓL hRL hL1 hLq hqs
  -- the conclusion
  have hmain : tr.cost ℓ * R ≤ ((22 + 2 * C₁) + 588 * cA + 2 * C₁ * (3 * C₁ + 18) + 9600 * cA +
      16128 * cA + (5 + c') * (26 + 4 * c' + 6 * C₁)) * s := by
    calc tr.cost ℓ * R ≤ (e * (2 * q₀ ^ 2 * S.fw + ℓ) + Λ + 2 * ℓ +
          (ℓ * (1 + D0) + trB ℓ Wm + e * (ℓ * (1 + Dm)) + Ξ)) * R := Nat.mul_le_mul_right _ htot
      _ = e * (2 * q₀ ^ 2 * S.fw + ℓ) * R + Λ * R +
          (2 * ℓ + ℓ * (1 + D0) + e * (ℓ * (1 + Dm))) * R + Ξ * R + trB ℓ Wm * R := by ring
      _ ≤ (22 + 2 * C₁) * s + 588 * cA * s + 2 * C₁ * (3 * C₁ + 18) * s + 20 * (480 * cA) * s +
          (16128 * cA * s + (5 + c') * (26 + 4 * c' + 6 * C₁) * s) := by gcongr
      _ = _ := by ring
  generalize hCst : ((22 + 2 * C₁) + 588 * cA + 2 * C₁ * (3 * C₁ + 18) + 9600 * cA +
      16128 * cA + (5 + c') * (26 + 4 * c' + 6 * C₁)) = Cst at hmain ⊢
  have hC : 0 < Cst := by rw [← hCst]; omega
  have hlt : s < R * (s / R + 1) := by
    have := Nat.lt_mul_div_succ s (show 0 < R by omega)
    omega
  have : tr.cost ℓ * R < Cst * (s / R + 1) * R := by
    calc tr.cost ℓ * R ≤ Cst * s := hmain
      _ < Cst * (R * (s / R + 1)) := Nat.mul_lt_mul_of_pos_left hlt hC
      _ = Cst * (s / R + 1) * R := by ring
  exact (Nat.lt_of_mul_lt_mul_right this).le

end Cslib.Complexity.NtimeDspace.Cube
