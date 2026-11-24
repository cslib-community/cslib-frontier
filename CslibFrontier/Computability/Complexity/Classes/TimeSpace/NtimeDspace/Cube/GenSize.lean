/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.GenBits

/-!
# The bits of `Z(G)` at the budget `O(s / √log s)`

`cube_bit` of `GenBits.lean` computes bit `P - 1` of `Z(G)` under the bundle `CubeTiers` at a
budget `L`. Here the hypotheses of `CubeTiers` that do not concern the input terms are discharged
for the setup of §4.3 of size `s` (`setupOf`), for every network with `s^{O(1)}` vertices, `O(s)`
edges, degrees `O(log s)` and vertex functions of size `s^{O(1)}`, at every budget
`L ≥ c₀ · SqrtLog s` with `SqrtLog s = s / ⌊√⌊log₂ s⌋⌋ + 1`:

* the setup is good and the cost of the formula is at most `C · SqrtLog s < L` (`formula_cost`,
  Lemma 6.3), and every state reached from the root has a code below `2^L` (`state_size`);
* `2K = 2^(2^D)` for `D = ⌊log₂ (⌊log₂ s⌋ / 3)⌋`, and the first clique `q₀ = 2K` satisfies
  `q₀³ ≤ s` and `⌊log₂ s⌋³ ≤ q₀` (`setup_facts`, the parameters of the proof of `formula_cost`),
  so `fw + q₀ < L` and `q₀² fw ≤ L`;
* `Φ₀ ≤ 64 ((4C₁ + 3) s)²` (`firstClique_potential`, Lemma 4.3 (a)) and `2^D > ⌊log₂ s⌋ / 6`, so
  `43200 Φ₀ + 3600 · 2^D < L² · 2^D`: this gives the argument codes (`3600 Φ₀ < L² 2^D`) and the
  reader fuel `B = L ≥ w(A) + 2` for the weight bound `A = 12 (Φ₀ / 2^D) + 1`.

## Main results

* `setup_facts`: the parameters of the setup of size `s`.
* `cube_bit_size`: **the bits of `Z(G)` at every budget `L ≥ c₀ · SqrtLog s`**, given the input
  values `CubeIn` (precision `P`, reader fuel and fuel `L`) and the tiers of the input terms.
-/

public section

namespace Cslib.Complexity.NtimeDspace.Cube.Num

open NtimeDspace.ProgTerm NtimeDspace.ProgTerm.Term SumProduct NtimeDspace.Cross

/-! ### The parameters of the setup -/

/-- **The parameters of the setup of size `s`** (from the proof of `formula_cost`): for
`D = ⌊log₂ (⌊log₂ s⌋ / 3)⌋` and `q₀ = 2K`, `q₀ = 2^(2^D)`, `q₀³ ≤ s`, `⌊log₂ s⌋³ ≤ q₀`,
`2^D ≤ ⌊log₂ s⌋ < 6 · 2^D`, `192 ≤ ⌊log₂ s⌋`, `Φ₀ ≤ 64 ((4C₁ + 3) s)²` and
`fw = 3 (⌊log₂ s⌋ + 1) + 5`. -/
theorem setup_facts (C₁ : ℕ) {s : ℕ} (hs : 2 ^ 192 + 48 * (4 * C₁ + 3) ^ 2 + C₁ + 1 ≤ s) {V : ℕ}
    (G : EdgeNet ℤ (Fin V)) (P : ℕ) (hM : G.M ≤ C₁ * (s + 1))
    (hdeg : ∀ v, (G.ports v).length ≤ C₁ * (Nat.log 2 s + 1)) :
    2 * (setupOf s G P).K = 2 ^ 2 ^ Nat.log 2 (Nat.log 2 s / 3) ∧
      (2 * (setupOf s G P).K) ^ 3 ≤ s ∧ Nat.log 2 s ^ 3 ≤ 2 * (setupOf s G P).K ∧
      2 ^ Nat.log 2 (Nat.log 2 s / 3) ≤ Nat.log 2 s ∧
      Nat.log 2 s < 6 * 2 ^ Nat.log 2 (Nat.log 2 s / 3) ∧ 192 ≤ Nat.log 2 s ∧
      (setupOf s G P).C₀.potential ≤ 64 * ((4 * C₁ + 3) * s) ^ 2 ∧
      (setupOf s G P).fw = 3 * (Nat.log 2 s + 1) + 5 := by
  generalize hcA : 4 * C₁ + 3 = cA at hs ⊢
  have hs48 : 48 * cA ^ 2 + 1 ≤ s := by omega
  have hs192 : 2 ^ 192 ≤ s := by omega
  generalize hL : Nat.log 2 s = L at hdeg ⊢
  have hL192 : 192 ≤ L := hL ▸ Nat.le_log_of_pow_le (by norm_num) hs192
  have hsL : 2 ^ L ≤ s := hL ▸ Nat.pow_log_le_self 2 (by omega)
  generalize he : Nat.log 2 (L / 3) = e
  have he6 : 6 ≤ e := he ▸ Nat.le_log_of_pow_le (by norm_num) (by omega)
  have hh3 : 2 ^ e ≤ L / 3 := he ▸ Nat.pow_log_le_self 2 (by omega)
  have hh6 : L < 6 * 2 ^ e := by
    have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (L / 3)
    rw [he, pow_succ] at this
    omega
  have hhs : hstar s = 2 ^ e := by rw [hstar, hL, he]
  have hK : (setupOf s G P).K = 2 ^ (2 ^ e - 1) := by rw [setupOf, hhs]
  have h2K : 2 * (setupOf s G P).K = 2 ^ 2 ^ e := by
    rw [hK, ← pow_succ']; congr 1; have := Nat.one_le_two_pow (n := e); omega
  have hq3 : (2 ^ 2 ^ e) ^ 3 ≤ s := by
    rw [← pow_mul]; exact (Nat.pow_le_pow_right (by norm_num) (by omega)).trans hsL
  have hLq : L ^ 3 ≤ 2 ^ 2 ^ e :=
    calc L ^ 3 ≤ (6 * 2 ^ e) ^ 3 := Nat.pow_le_pow_left hh6.le 3
      _ = 216 * (2 ^ e) ^ 3 := by ring
      _ ≤ 2 ^ 2 ^ e := two_pow_cube_le e he6
  refine ⟨h2K, h2K ▸ hq3, h2K ▸ hLq, by omega, hh6, hL192, ?_, by rw [setupOf, hL]⟩
  -- the potential, as in the proof of `formula_cost`
  generalize hq₀ : 2 ^ 2 ^ e = q₀ at hq3 hLq h2K
  have hL1 : 1 ≤ L := by omega
  have hLq0 : L ≤ q₀ := (Nat.le_self_pow (by norm_num) L).trans hLq
  have hq1 : 1 ≤ q₀ := hq₀ ▸ Nat.one_le_two_pow
  have hq2s : q₀ ^ 2 ≤ s := (Nat.pow_le_pow_right hq1 (by norm_num)).trans hq3
  have hK1 : 1 ≤ (setupOf s G P).K := hK ▸ Nat.one_le_two_pow
  have hKq : (setupOf s G P).K ≤ q₀ := by omega
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

/-! ### The bits at the budget -/

theorem sqrtLog_eq (s : ℕ) : SqrtLog s = s / Nat.sqrt (Nat.log 2 s) + 1 := by
  rw [SqrtLog, Nat.log2_eq_log_two]

/-- `w(a) + 2 ≤ L` from `3600 a < L²`, for `a ≥ 1`. -/
theorem codeWidth_add_two_le {a L : ℕ} (ha : 1 ≤ a) (h : 3600 * a < L ^ 2) :
    codeWidth a + 2 ≤ L := by
  have h1 := codeWidth_sq_le a
  have h2 : 2 ≤ codeWidth a := by
    unfold codeWidth; rw [ite_eq_right (show ¬ a = 0 by omega)]; omega
  generalize codeWidth a = c at h1 h2 ⊢
  have h4 : (c + 2) ^ 2 ≤ 4 * c ^ 2 := by nlinarith
  have h3 : (c + 2) ^ 2 < L ^ 2 := by omega
  exact (lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le _) h3).le

theorem pot_aux (a s : ℕ) :
    6 * (43200 * (64 * (a * s) ^ 2) + 3600 * s) ≤ (5000 * (a + 1)) ^ 2 * (s + 1) ^ 2 := by
  have hs : s ^ 2 ≤ (s + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hs1 : s ≤ (s + 1) ^ 2 := by nlinarith
  have ha : 16588800 * a ^ 2 + 21600 ≤ (5000 * (a + 1)) ^ 2 := by
    have e : (5000 * (a + 1)) ^ 2 = 25000000 * a ^ 2 + 50000000 * a + 25000000 := by ring
    omega
  calc 6 * (43200 * (64 * (a * s) ^ 2) + 3600 * s) = 16588800 * a ^ 2 * s ^ 2 + 21600 * s := by
        ring
    _ ≤ 16588800 * a ^ 2 * (s + 1) ^ 2 + 21600 * (s + 1) ^ 2 :=
        Nat.add_le_add (Nat.mul_le_mul_left _ hs) (Nat.mul_le_mul_left _ hs1)
    _ = (16588800 * a ^ 2 + 21600) * (s + 1) ^ 2 := by ring
    _ ≤ (5000 * (a + 1)) ^ 2 * (s + 1) ^ 2 := Nat.mul_le_mul_right _ ha

/-- **The bits of `Z(G)` at the budget `O(s / √log s)`.** For every `C₁ ≥ 2` there are `c₀` and
`s₀` such that for every `s ≥ s₀` and every budget `L ≥ c₀ · SqrtLog s`, every network with at most
`(s+2)^C₁` vertices, at most `C₁ (s+1)` edges, degrees at most `C₁ (⌊log₂ s⌋ + 1)` and nonnegative
vertex functions of value at most `(s+2)^C₁` (at arguments of the right length), and every precision
`1 ≤ P ≤ 2^(C₁ (⌊log₂ s⌋ + 1))`: at a parameter whose input terms have the values of the setup
`setupOf s G P` with reader fuel and fuel `L`, and the tiers of `CubeTiers` at `L`, the evaluator
`formulaBitT T` returns bit `P - 1` of `Z(G)` with every value below `2^(128 L)`. -/
theorem cube_bit_size (C₁ : ℕ) (hC₁ : 2 ≤ C₁) : ∃ c₀ s₀ : ℕ, ∀ s, s₀ ≤ s → ∀ L,
    c₀ * SqrtLog s ≤ L → ∀ {V : ℕ} (G : EdgeNet ℤ (Fin V)) (P : ℕ), V ≤ (s + 2) ^ C₁ →
    G.M ≤ C₁ * (s + 1) → (∀ v, (G.ports v).length ≤ C₁ * (Nat.log 2 s + 1)) →
    (∀ v l, l.length = (G.ports v).length → |G.eval v l| ≤ ((s + 2) ^ C₁ : ℕ)) →
    EvalNonneg G → 1 ≤ P → P ≤ 2 ^ (C₁ * (Nat.log 2 s + 1)) →
    ∀ {w : List Bool} {par : ℕ} {T : CubeT},
      CubeIn G w par T P L (setupOf s G P).fw (setupOf s G P).K L →
      NetTiers G w L [par] T.N → Tm w L 1 T.PT [par] → Tm w L 1 T.BT [par] →
      Tm w L 1 T.fwT [par] → Tm w L 1 T.KT [par] → Tm w L 1 T.HT [par] →
      (formulaBitT T).denote w [par] = G.value.toNat / 2 ^ (P - 1) % 2 ∧
        (formulaBitT T).Bnd w (2 ^ (128 * L)) [par] := by
  obtain ⟨Cf, sf, hfc⟩ := formula_cost C₁
  obtain ⟨Cs, ss, hss⟩ := state_size C₁
  refine ⟨Cf + Cs + C₁ + 5000 * (4 * C₁ + 4) + 16, sf + ss + 2 ^ 192 + 48 *
      (4 * C₁ + 3) ^ 2 + C₁ + 1,
    ?_⟩
  intro s hs L hL V G P hV hM hdeg hev hnn hP1 hPℓ w par T hI hN tP tB tfw tK tH
  obtain ⟨h2K, hq3, hlq, hDl, hlD, hl192, hΦ, hfw⟩ :=
    setup_facts C₁ (s := s) (by omega) G P hM hdeg
  obtain ⟨hGood, hcost⟩ := hfc s (by omega) G P (C₁ * (Nat.log 2 s + 1)) hV hM hdeg le_rfl
  have hcode := hss s (by omega) G P hV hM hdeg hev
  -- the scale
  rw [sqrtLog_eq] at hL
  have hl2 := log2_add_one_le_sqrtLog s
  rw [sqrtLog_eq, Nat.log2_eq_log_two] at hl2
  generalize hR : Nat.sqrt (Nat.log 2 s) = R at hL hcost hcode hl2
  generalize hlg : Nat.log 2 s = lg at hR hlq hDl hlD hl192 hfw hl2 hPℓ h2K hcost
  generalize hD : Nat.log 2 (lg / 3) = D at h2K hDl hlD
  generalize hc₀ : Cf + Cs + C₁ + 5000 * (4 * C₁ + 4) + 16 = c₀ at hL
  generalize hΦ₀ : (setupOf s G P).C₀.potential = Φ₀ at hΦ
  have hR2 : R ^ 2 ≤ lg := hR ▸ Nat.sqrt_le' lg
  have hR1 : 1 ≤ R := hR ▸ Nat.le_sqrt'.mpr (by omega)
  have hRl : R ≤ lg := (Nat.le_self_pow (by norm_num) R).trans hR2
  have hSL : s + 1 ≤ R * (s / R + 1) := Nat.lt_mul_div_succ s (by omega)
  have hLR : c₀ * (s + 1) ≤ L * R :=
    calc c₀ * (s + 1) ≤ c₀ * (R * (s / R + 1)) := Nat.mul_le_mul_left _ hSL
      _ = c₀ * (s / R + 1) * R := by ring
      _ ≤ L * R := Nat.mul_le_mul_right _ hL
  generalize hF : s / R + 1 = F at hL hcost hcode hl2 hSL
  generalize hq₀ : 2 * (setupOf s G P).K = q₀ at h2K hq3 hlq
  have hq1 : 1 ≤ q₀ := by rw [h2K]; exact Nat.one_le_two_pow
  have hlq0 : lg ≤ q₀ := (Nat.le_self_pow (by norm_num) lg).trans hlq
  have hq2 : q₀ ^ 2 ≤ s := (Nat.pow_le_pow_right hq1 (by norm_num)).trans hq3
  have hl2q : lg ^ 2 ≤ q₀ := (Nat.pow_le_pow_right (by omega) (by norm_num)).trans hlq
  have hLF : c₀ * F ≤ L := hL
  have hF1 : 1 ≤ F := by omega
  have hc16 : 16 ≤ c₀ := by omega
  have hLs : 16 * (s + 1) ≤ L * R := le_trans (Nat.mul_le_mul_right _ hc16) hLR
  have hL16 : 16 ≤ L := le_trans hc16 (le_trans (Nat.le_mul_of_pos_right _ hF1) hLF)
  -- the size conditions
  have hfwl : (setupOf s G P).fw ≤ 11 * lg := by omega
  have hq : (setupOf s G P).fw + 2 * (setupOf s G P).K < L := by
    rw [hq₀]
    have h1 : ((setupOf s G P).fw + q₀) * R ≤ 12 * s :=
      calc ((setupOf s G P).fw + q₀) * R ≤ (12 * q₀) * q₀ :=
            Nat.mul_le_mul (by omega) (hRl.trans hlq0)
        _ = 12 * q₀ ^ 2 := by ring
        _ ≤ 12 * s := Nat.mul_le_mul_left _ hq2
    have h2 : 12 * s < L * R := by omega
    exact Nat.lt_of_mul_lt_mul_right (h1.trans_lt h2)
  have hArr : 2 * (setupOf s G P).K * (2 * (setupOf s G P).K) * (setupOf s G P).fw ≤ L := by
    rw [hq₀]
    have h1 : q₀ * q₀ * (setupOf s G P).fw * R ≤ 11 * s :=
      calc q₀ * q₀ * (setupOf s G P).fw * R ≤ q₀ * q₀ * (11 * lg) * lg :=
            Nat.mul_le_mul (Nat.mul_le_mul_left _ hfwl) hRl
        _ = 11 * (q₀ * q₀ * lg ^ 2) := by ring
        _ ≤ 11 * (q₀ * q₀ * q₀) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hl2q)
        _ = 11 * q₀ ^ 3 := by ring
        _ ≤ 11 * s := Nat.mul_le_mul_left _ hq3
    have h2 : 11 * s < L * R := by omega
    exact (Nat.lt_of_mul_lt_mul_right (h1.trans_lt h2)).le
  -- the potential
  have hkey : 43200 * Φ₀ + 3600 * 2 ^ D < L ^ 2 * 2 ^ D := by
    have h1 : c₀ ^ 2 * (s + 1) ^ 2 ≤ L ^ 2 * R ^ 2 := by
      rw [← mul_pow, ← mul_pow]; exact Nat.pow_le_pow_left hLR 2
    have h2 : L ^ 2 * R ^ 2 < 6 * (L ^ 2 * 2 ^ D) := by
      have : 0 < L ^ 2 := pow_pos (by omega) 2
      calc L ^ 2 * R ^ 2 ≤ L ^ 2 * lg := Nat.mul_le_mul_left _ hR2
        _ < L ^ 2 * (6 * 2 ^ D) := Nat.mul_lt_mul_of_pos_left hlD this
        _ = 6 * (L ^ 2 * 2 ^ D) := by ring
    have h3 : 6 * (43200 * Φ₀ + 3600 * 2 ^ D) ≤ c₀ ^ 2 * (s + 1) ^ 2 := by
      have hc : 5000 * (4 * C₁ + 4) ≤ c₀ := by omega
      have hc2 : (5000 * (4 * C₁ + 4)) ^ 2 ≤ c₀ ^ 2 := Nat.pow_le_pow_left hc 2
      have hDs : 2 ^ D ≤ s := hDl.trans (hlg ▸ (Nat.log_le_self 2 s))
      calc 6 * (43200 * Φ₀ + 3600 * 2 ^ D)
          ≤ 6 * (43200 * (64 * ((4 * C₁ + 3) * s) ^ 2) + 3600 * s) :=
            Nat.mul_le_mul_left _ (Nat.add_le_add (Nat.mul_le_mul_left _ hΦ)
              (Nat.mul_le_mul_left _ hDs))
        _ ≤ (5000 * (4 * C₁ + 3 + 1)) ^ 2 * (s + 1) ^ 2 := pot_aux _ _
        _ ≤ c₀ ^ 2 * (s + 1) ^ 2 := Nat.mul_le_mul_right _ hc2
    omega
  have harg : 3600 * Φ₀ < L ^ 2 * 2 ^ D := by omega
  have hA1 : 1 ≤ 12 * (Φ₀ / 2 ^ D) + 1 := by omega
  have hB : codeWidth (12 * (Φ₀ / 2 ^ D) + 1) + 2 ≤ L := by
    refine codeWidth_add_two_le hA1 ?_
    have h1 : (12 * (Φ₀ / 2 ^ D) + 1) * 2 ^ D ≤ 12 * Φ₀ + 2 ^ D := by
      have := Nat.div_mul_le_self Φ₀ (2 ^ D)
      rw [add_mul, one_mul, mul_assoc]; omega
    have h2 : 3600 * (12 * (Φ₀ / 2 ^ D) + 1) * 2 ^ D < L ^ 2 * 2 ^ D :=
      calc 3600 * (12 * (Φ₀ / 2 ^ D) + 1) * 2 ^ D
          = 3600 * ((12 * (Φ₀ / 2 ^ D) + 1) * 2 ^ D) := by ring
        _ ≤ 3600 * (12 * Φ₀ + 2 ^ D) := Nat.mul_le_mul_left _ h1
        _ = 43200 * Φ₀ + 3600 * 2 ^ D := by ring
        _ < L ^ 2 * 2 ^ D := hkey
    exact Nat.lt_of_mul_lt_mul_right h2
  -- the bundle
  have hG : CubeTiers (setupOf s G P) w L par T D (12 * (Φ₀ / 2 ^ D) + 1) L :=
    { hT := hN, tP := tP, tB := tB, tfw := tfw, tK := tK, tH := tH, hS := hGood, hnn := hnn
      he := hq₀.trans h2K, hA := by rw [hΦ₀], hB := hB, hBL := le_rfl, hq := hq
      harg := by rw [hΦ₀]; exact harg, hArr := hArr
      hcode := fun st h => (hcode st h).trans_le (Nat.pow_le_pow_right (by norm_num)
        (le_trans (Nat.mul_le_mul_right _ (by omega)) hLF)) }
  have hℓ : 2 ≤ C₁ * (lg + 1) := le_trans hC₁ (Nat.le_mul_of_pos_right _ (by omega))
  have hℓL : C₁ * (lg + 1) < L :=
    calc C₁ * (lg + 1) ≤ C₁ * F := Nat.mul_le_mul_left _ hl2
      _ < c₀ * F := Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
      _ ≤ L := hLF
  have hcL : Cf * F < L :=
    calc Cf * F < c₀ * F := Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
      _ ≤ L := hLF
  have hPL : P < 2 ^ L := hPℓ.trans_lt (Nat.pow_lt_pow_right (by norm_num) hℓL)
  exact cube_bit (S := setupOf s G P) (j := P - 1) hI hG (show P = P - 1 + 1 by omega) hPL
      hℓ hPℓ hcost hcL

end Cslib.Complexity.NtimeDspace.Cube.Num
