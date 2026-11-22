/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.ExactBitsBd

/-!
# The Chinese remainder step, elementary version: the bits of a number from a residue program

`exists_bitsProg` is the abstract form of the Chinese remainder step of the residue route. From
programs `Hq, Xq, Eq, Wq` closed over `[τ]` (the window `(H, X]`, the exponent `E` and the width
`W`) and a residue program
`q` closed over `[τ, n, p]`, it builds one program `P` closed over `[τ, n, j]` such that, whenever
the residues are those of a number `0 ≤ Z ≤ 2^E` at the primes of a window with product above
`2^(E+1)`, `P` computes bit `j` of `Z` for every `j`, with every value at most `M`, provided

* `M` bounds the parameter programs and the residue program,
* `2 ≤ W`, `X + 1 ≤ 2^(W-1)`, `E + 1 ≤ M`, and
* `4 (X + 1) 2^W (W^g + 1) ≤ M` for `g = E / ⌊W / (⌊log₂ X⌋ + 1)⌋ + 1`.

The last condition is where the elementary construction differs from the logspace conversion of
Chiu, Davida and Litow: with `M = 2^(C·F)` it asks `W ≤ F` and `g log₂ W ≤ F`, that is roughly
`F² ≥ E · log₂ X · log₂ F`, while that conversion needs only `F ≥ log S`. In the residue route,
`F = τ/√log τ` and `E, log X = O(τ), O(log τ)`, so the condition holds with room to spare. The
current paper computes the bits directly and has no such step.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Cross.Exact

open NtimeDspace.ProgLang NtimeDspace.ProgTerm Term NtimeDspace.SumProduct Finset

variable {w : List Bool} {env : List ℕ} {M : ℕ} {c : Ctx} {s : SC} {q : Prog}

/-! ### Bounds of the columns and the chains -/

theorem colA_le (H X E W r g : ℕ) (res : ℕ → ℕ) (i : ℕ) :
    colA H X E W r g res i ≤ (X + 1) * W ^ g := by
  unfold colA
  calc _ ≤ ∑ _p ∈ range (X + 1), W ^ g := sum_le_sum fun p _ => by
        split_ifs
        · calc _ ≤ ∑ _u ∈ range (W ^ g), 1 := sum_le_sum fun u _ => by
                split_ifs
                · exact pbits_le_one _ _ _ _
                · exact Nat.zero_le _
            _ = W ^ g := by simp
        · exact Nat.zero_le _
    _ = (X + 1) * W ^ g := by simp

theorem colQ_le (H X E W r g i : ℕ) : colQ H X E W r g i ≤ W ^ g := by
  unfold colQ
  calc _ ≤ ∑ _u ∈ range (W ^ g), 1 := sum_le_sum fun u _ => by
        split_ifs
        · exact pbits_le_one _ _ _ _
        · exact Nat.zero_le _
    _ = W ^ g := by simp

theorem kq_le (H X E W : ℕ) (res : ℕ → ℕ) (hX : X + 1 ≤ 2 ^ W) : kq H X E W res ≤ X + 2 := by
  unfold kq
  have h1 : (∑ p ∈ range (X + 1), if sel H X E p then bco H X E res p * 2 ^ W / p else 0) ≤
      (X + 1) * 2 ^ W := by
    calc _ ≤ ∑ _p ∈ range (X + 1), 2 ^ W := sum_le_sum fun p _ => by
          split_ifs with h
          · have hp := (sel_prime h).pos
            have : bco H X E res p < p := Nat.mod_lt _ hp
            exact Nat.div_le_of_le_mul (Nat.mul_le_mul_right _ this.le)
          · exact Nat.zero_le _
      _ = (X + 1) * 2 ^ W := by simp
  have h2 : (∑ p ∈ range (X + 1), if sel H X E p then 1 else 0) ≤ X + 1 := by
    calc _ ≤ ∑ _p ∈ range (X + 1), 1 := sum_le_sum fun p _ => by split_ifs <;> omega
      _ = X + 1 := by simp
  have hpos : 0 < 2 ^ W := Nat.two_pow_pos W
  calc _ ≤ ((X + 1) * 2 ^ W + (X + 1)) / 2 ^ W := Nat.div_le_div_right (by omega)
    _ ≤ X + 2 := by
        refine Nat.div_le_of_le_mul ?_
        have e : 2 ^ W * (X + 2) = (X + 1) * 2 ^ W + 2 ^ W := by ring
        omega

namespace Sizes

variable (hs : Sizes s M)
include hs

theorem chain_bound : 2 * ((s.X + 2) * s.W ^ s.g + 2) ≤ M := by
  have h := hs.hM
  have h2 : 4 ≤ 2 ^ s.W := by
    calc 4 = 2 ^ 2 := rfl
      _ ≤ 2 ^ s.W := Nat.pow_le_pow_right (by norm_num) hs.hW
  have : (s.X + 1) * 4 * (s.W ^ s.g + 1) ≤ (s.X + 1) * 2 ^ s.W * (s.W ^ s.g + 1) := by gcongr
  have e : (s.X + 1) * 4 * (s.W ^ s.g + 1) = 4 * ((s.X + 1) * s.W ^ s.g) + 4 * (s.X + 1) := by ring
  have e2 : (s.X + 2) * s.W ^ s.g = (s.X + 1) * s.W ^ s.g + s.W ^ s.g := by ring
  have := hs.one_le_Wg
  have : s.W ^ s.g ≤ (s.X + 1) * s.W ^ s.g := Nat.le_mul_of_pos_left _ (by omega)
  omega

end Sizes

theorem bd_chainT {col : Term → Term} {C : ℕ → ℕ} (hcol : FVal w col env C) {D : ℕ}
    {j : Term} {a : ℕ} (hj : Val w j env a) (hbj : Bd w M j env) (ha : a ≤ M)
    (hC : ∀ k ≤ a, C k ≤ D) (hD : 2 * D ≤ M) (h2 : 2 ≤ M)
    (hbcol : ∀ pre u k, k ≤ a → Val w u (pre ++ env) k → Bd w M u (pre ++ env) →
      Bd w M (col u) (pre ++ env)) : Bd w M (chainT col j) env := by
  refine bd_foldT hj (val_const 0 env) (fun acc i => (C i + acc) / 2)
    (fun pre u u' p k hu hu' => val_div (val_add (hcol pre u' k hu') hu) (val_const 2 _))
    hbj (bd_const (Nat.zero_le _) _) ha fun pre u u' p k hk hp hu hu' hbu hbu' => ?_
  have hch : p ≤ D := by
    rw [hp]; exact chain_le_of_lt (J := a) (fun i hi => hC i hi.le) k hk.le
  exact bd_div (bd_add (hbcol pre u' k hk.le hu' hbu') hbu (hcol pre u' k hu') hu
    (by have := hC k hk.le; omega)) (bd_const h2 _)

theorem bd_bitOfT {col : Term → Term} {C : ℕ → ℕ} (hcol : FVal w col env C) {D : ℕ}
    {j : Term} {a : ℕ} (hj : Val w j env a) (hbj : Bd w M j env) (ha : a ≤ M)
    (hC : ∀ k ≤ a, C k ≤ D) (hD : 2 * D ≤ M) (h2 : 2 ≤ M)
    (hbcol : ∀ pre u k, k ≤ a → Val w u (pre ++ env) k → Bd w M u (pre ++ env) →
      Bd w M (col u) (pre ++ env)) : Bd w M (bitOfT col j) env := by
  have hch : chain C a ≤ D := chain_le_of_lt (J := a + 1) (fun i hi => hC i (by omega)) a (by omega)
  refine bd_mod (bd_add (hbcol [] j a le_rfl (by simpa using hj) (by simpa using hbj))
    (bd_chainT hcol hj hbj ha hC hD h2 hbcol) (hcol [] j a (by simpa using hj)) (val_chainT hcol hj)
    (by have := hC a le_rfl; omega)) (bd_const h2 _)

/-! ### Bounds of the columns -/

theorem bd_colAT (hq : Prog'.closed 3 q = true) (hc : c.Good w s env) (hcb : c.GoodB w M env)
    (hs : Sizes s M) (hR : ResOK w q s M) {i : Term} {a : ℕ} (hi : Val w i env a)
    (hbi : Bd w M i env) (ha : a ≤ M) : Bd w M (colAT q c i) env := by
  have h4 := hs.four_le
  refine bd_sumT (val_add hc.2.2.2.1 (val_const 1 env))
    (F := fun p => if sel s.H s.X s.E p then ∑ u ∈ range (s.W ^ s.g),
      (if sdig s.W s.g u = a then pbits s.W s.g (fac s.H s.X s.E s.r (resOf w q s) p) u else 0)
      else 0) ?_ (bd_add hcb.2.2.2.1 (bd_const (by omega) _) hc.2.2.2.1 (val_const 1 _) hs.X1_le)
    hs.X1_le ?_ ?_
  · -- the meaning of the body (as in `val_colAT`)
    intro pre p v hp
    have := (val_colAT (i := i) hq hc hi)
    exact fun extra => by
      have hc' := hc.ext pre
      by_cases hsv : sel s.H s.X s.E v
      · have hv : 2 ≤ v := (sel_prime hsv).two_le
        have hin := val_sumT (n := c.Wg) hc'.2.2.2.2.2.2.2.2
          (body := fun u => ite (eqT (sdigT c u) i) (pbitsT c (facT q c p) u) (const 0))
          (F := fun u => if sdig s.W s.g u = a then
            pbits s.W s.g (fac s.H s.X s.E s.r (resOf w q s) v) u else 0)
          fun pre' u b hu => by
            have hc'' := hc'.ext pre'
            have := val_ite (val_eqT (val_sdigT hc'' hu) ((hi.ext pre).ext pre'))
              (val_pbitsT hc'' (fun pre'' m k hm => val_facT hq (hc''.ext pre'')
                ((hp.ext pre').ext pre'') hv hm) hu) (val_const 0 _)
            refine fun extra => (this extra).trans ?_
            by_cases h : sdig s.W s.g b = a <;> simp [h]
        have := val_ite (val_selT hc' hp) hin (val_const 0 _)
        exact (this extra).trans (by simp [hsv])
      · show (ite (selT c p) _ (const 0)).denote w _ = _
        rw [denote_ite, val_selT hc' hp extra]
        simp [hsv]
  · calc _ ≤ ∑ _p ∈ range (s.X + 1), s.W ^ s.g := sum_le_sum fun p _ => by
          split_ifs
          · calc _ ≤ ∑ _u ∈ range (s.W ^ s.g), 1 := sum_le_sum fun u _ => by
                  split_ifs
                  · exact pbits_le_one _ _ _ _
                  · exact Nat.zero_le _
              _ = s.W ^ s.g := by simp
          · exact Nat.zero_le _
      _ = (s.X + 1) * s.W ^ s.g := by simp
      _ ≤ M := hs.col_le
  · intro pre p v hv hp hbp
    have hc' := hc.ext pre
    have hcb' := hcb.ext pre
    have hvM : v ≤ M := by have := hs.X1_le; omega
    refine bd_ite (bd_selT hc' hcb' hs hp hbp hvM) (val_selT hc' hp) (fun hpos => ?_)
      fun _ => bd_const (Nat.zero_le _) _
    have hsv : sel s.H s.X s.E v := by by_contra h; simp [h] at hpos
    have hv2 : 2 ≤ v := (sel_prime hsv).two_le
    refine bd_sumT hc'.2.2.2.2.2.2.2.2
      (F := fun u => if sdig s.W s.g u = a then
        pbits s.W s.g (fac s.H s.X s.E s.r (resOf w q s) v) u else 0) ?_ hcb'.2.2.2.2.2.2.2.2
      hs.Wg_le ?_ fun pre' u b hb hu hbu => ?_
    · intro pre' u b hu
      have hc'' := hc'.ext pre'
      have := val_ite (val_eqT (val_sdigT hc'' hu) ((hi.ext pre).ext pre'))
        (val_pbitsT hc'' (fun pre'' m k hm => val_facT hq (hc''.ext pre'')
          ((hp.ext pre').ext pre'') hv2 hm) hu) (val_const 0 _)
      refine fun extra => (this extra).trans ?_
      by_cases h : sdig s.W s.g b = a <;> simp [h]
    · calc _ ≤ ∑ _u ∈ range (s.W ^ s.g), 1 := sum_le_sum fun u _ => by
            split_ifs
            · exact pbits_le_one _ _ _ _
            · exact Nat.zero_le _
        _ = s.W ^ s.g := by simp
        _ ≤ M := hs.Wg_le
    · have hc'' := hc'.ext pre'
      have hcb'' := hcb'.ext pre'
      have hsd : sdig s.W s.g b ≤ M := (sdig_le (by have := hs.hW; omega) b).trans hs.gW'_le
      refine bd_ite (bd_eqT (bd_sdigT hc'' hcb'' hs hu hbu) ((hbi.ext pre).ext pre')
        (val_sdigT hc'' hu) ((hi.ext pre).ext pre') hsd ha (by omega))
        (val_eqT (val_sdigT hc'' hu) ((hi.ext pre).ext pre')) (fun _ => ?_)
        fun _ => bd_const (Nat.zero_le _) _
      refine bd_pbitsT hc'' hcb'' hs (fun pre'' m k hm => val_facT hq (hc''.ext pre'')
        ((hp.ext pre').ext pre'') hv2 hm) (fun pre'' m k hk hm hbm => ?_) hu hbu
      exact bd_facT hq (hc''.ext pre'') (hcb''.ext pre'') hs hR ((hp.ext pre').ext pre'')
        ((hbp.ext pre').ext pre'') hsv hm hbm (hk.le.trans hs.g_le)

theorem bd_colQT (hc : c.Good w s env) (hcb : c.GoodB w M env) (hs : Sizes s M) {i : Term}
    {a : ℕ} (hi : Val w i env a) (hbi : Bd w M i env) (ha : a ≤ M) : Bd w M (colQT c i) env := by
  have h4 := hs.four_le
  refine bd_sumT hc.2.2.2.2.2.2.2.2
    (F := fun u => if sdig s.W s.g u = a then pbits s.W s.g (Qm s.H s.X s.E s.r) u else 0) ?_
    hcb.2.2.2.2.2.2.2.2 hs.Wg_le ?_ fun pre u b hb hu hbu => ?_
  · intro pre u b hu
    have hc' := hc.ext pre
    have := val_ite (val_eqT (val_sdigT hc' hu) (hi.ext pre))
      (val_pbitsT hc' (fun pre' m k hm => val_QmT (hc'.ext pre') hm) hu) (val_const 0 _)
    refine fun extra => (this extra).trans ?_
    by_cases h : sdig s.W s.g b = a <;> simp [h]
  · calc _ ≤ ∑ _u ∈ range (s.W ^ s.g), 1 := sum_le_sum fun u _ => by
          split_ifs
          · exact pbits_le_one _ _ _ _
          · exact Nat.zero_le _
      _ = s.W ^ s.g := by simp
      _ ≤ M := hs.Wg_le
  · have hc' := hc.ext pre
    have hcb' := hcb.ext pre
    have hsd : sdig s.W s.g b ≤ M := (sdig_le (by have := hs.hW; omega) b).trans hs.gW'_le
    refine bd_ite (bd_eqT (bd_sdigT hc' hcb' hs hu hbu) (hbi.ext pre) (val_sdigT hc' hu)
      (hi.ext pre) hsd ha (by omega)) (val_eqT (val_sdigT hc' hu) (hi.ext pre)) (fun _ => ?_)
      fun _ => bd_const (Nat.zero_le _) _
    exact bd_pbitsT hc' hcb' hs (fun pre' m k hm => val_QmT (hc'.ext pre') hm)
      (fun pre' m k hk hm hbm => bd_QmT (hc'.ext pre') (hcb'.ext pre') hs hm hbm
        (hk.le.trans hs.g_le)) hu hbu

theorem bd_kqT (hq : Prog'.closed 3 q = true) (hc : c.Good w s env) (hcb : c.GoodB w M env)
    (hs : Sizes s M) (hR : ResOK w q s M) : Bd w M (kqT q c) env := by
  have h4 := hs.four_le
  have h2W := val_pwT (val_const 2 env) hc.2.2.2.2.2.1
  have hb2W : Bd w M (pwT (const 2) c.W) env :=
    bd_pwT (val_const 2 env) hc.2.2.2.2.2.1 (bd_const (by omega) _) hcb.2.2.2.2.2.1 le_rfl
      hs.two_pow_le (by omega) (Nat.lt_two_pow_self.le.trans hs.two_pow_le)
  have hX1 := bd_add hcb.2.2.2.1 (bd_const (by omega) _) hc.2.2.2.1 (val_const 1 env) hs.X1_le
  set F1 := fun p => if sel s.H s.X s.E p then bco s.H s.X s.E (resOf w q s) p * 2 ^ s.W / p else 0
  have hF1 : FVal w (fun p => ite (selT c p) (div (mul (bT q c p) (pwT (const 2) c.W)) p)
      (const 0)) env F1 := fun pre p v hp => by
    have hc' := hc.ext pre
    by_cases hs' : sel s.H s.X s.E v
    · have := val_ite (val_selT hc' hp) (val_div (val_mul (val_bT hq hc' hp
        (sel_prime hs').two_le) (h2W.ext pre)) hp) (val_const 0 _)
      refine fun extra => (this extra).trans ?_
      simp [F1, hs']
    · refine fun extra => ?_
      show (ite (selT c p) _ (const 0)).denote w _ = _
      rw [denote_ite, val_selT hc' hp extra]
      simp [F1, hs']
  have hF2 : FVal w (fun p => selT c p) env (fun p => if sel s.H s.X s.E p then 1 else 0) :=
    fun pre p v hp => val_selT (hc.ext pre) hp
  have hs1 : ∑ p ∈ range (s.X + 1), F1 p ≤ (s.X + 1) * 2 ^ s.W := by
    calc _ ≤ ∑ _p ∈ range (s.X + 1), 2 ^ s.W := sum_le_sum fun p _ => by
          simp only [F1]
          split_ifs with h
          · have hp := (sel_prime h).pos
            have : bco s.H s.X s.E (resOf w q s) p < p := Nat.mod_lt _ hp
            exact Nat.div_le_of_le_mul (Nat.mul_le_mul_right _ this.le)
          · exact Nat.zero_le _
      _ = (s.X + 1) * 2 ^ s.W := by simp
  have hs2 : ∑ p ∈ range (s.X + 1), (if sel s.H s.X s.E p then 1 else 0) ≤ s.X + 1 := by
    calc _ ≤ ∑ _p ∈ range (s.X + 1), 1 := sum_le_sum fun p _ => by split_ifs <;> omega
      _ = s.X + 1 := by simp
  have hk := hs.kq_le_bound
  refine bd_div (bd_add (bd_sumT (val_add hc.2.2.2.1 (val_const 1 env)) hF1 hX1 hs.X1_le
      (by omega) fun pre p v hv hp hbp => ?_)
    (bd_sumT (val_add hc.2.2.2.1 (val_const 1 env)) hF2 hX1 hs.X1_le (by omega)
      fun pre p v hv hp hbp => bd_selT (hc.ext pre) (hcb.ext pre) hs hp hbp
        (by have := hs.X1_le; omega))
    (val_sumT (val_add hc.2.2.2.1 (val_const 1 env)) hF1)
    (val_sumT (val_add hc.2.2.2.1 (val_const 1 env)) hF2) (by omega)) hb2W
  have hc' := hc.ext pre
  have hcb' := hcb.ext pre
  have hvM : v ≤ M := by have := hs.X1_le; omega
  refine bd_ite (bd_selT hc' hcb' hs hp hbp hvM) (val_selT hc' hp) (fun hpos => ?_)
    fun _ => bd_const (Nat.zero_le _) _
  have hsv : sel s.H s.X s.E v := by by_contra h; simp [h] at hpos
  refine bd_div (bd_mul (bd_bT hq hc' hcb' hs hR hp hbp hsv) (hb2W.ext pre)
    (val_bT hq hc' hp (sel_prime hsv).two_le) (h2W.ext pre) ?_) hbp
  have : bco s.H s.X s.E (resOf w q s) v < v := Nat.mod_lt _ (sel_prime hsv).pos
  calc bco s.H s.X s.E (resOf w q s) v * 2 ^ s.W ≤ (s.X + 1) * 2 ^ s.W :=
        Nat.mul_le_mul_right _ (by have := sel_le hsv; omega)
    _ ≤ M := by omega

theorem bd_colZT (hq : Prog'.closed 3 q = true) (hc : c.Good w s env) (hcb : c.GoodB w M env)
    (hs : Sizes s M) (hR : ResOK w q s M) {k : Term}
    (hk : Val w k env (kq s.H s.X s.E s.W (resOf w q s))) (hbk : Bd w M k env) {i : Term}
    {a : ℕ} (hi : Val w i env a) (hbi : Bd w M i env) (ha : a ≤ M) :
    Bd w M (colZT q c k i) env := by
  have h4 := hs.four_le
  have hcol : FVal w (fun i => mul k (colQT c i)) env
      (fun i => kq s.H s.X s.E s.W (resOf w q s) * colQ s.H s.X s.E s.W s.r s.g i) :=
    fun pre u b hu => val_mul (hk.ext pre) (val_colQT (hc.ext pre) hu)
  have hD := hs.chain_bound
  have hCle : ∀ b, kq s.H s.X s.E s.W (resOf w q s) * colQ s.H s.X s.E s.W s.r s.g b ≤
      (s.X + 2) * s.W ^ s.g + 2 := fun b =>
    (Nat.mul_le_mul (kq_le _ _ _ _ _ hs.X1_le_two_pow) (colQ_le _ _ _ _ _ _ _)).trans (by omega)
  have hbit := bd_bitOfT hcol hi hbi ha (fun b _ => hCle b) hD (by omega)
    fun pre u b hb hu hbu => bd_mul (hbk.ext pre) (bd_colQT (hc.ext pre) (hcb.ext pre) hs hu hbu
      (hb.trans ha)) (hk.ext pre) (val_colQT (hc.ext pre) hu) ((hCle b).trans (by omega))
  have hA := colA_le s.H s.X s.E s.W s.r s.g (resOf w q s) a
  refine bd_add (bd_add (bd_colAT hq hc hcb hs hR hi hbi ha) (bd_sub (bd_const (by omega) _) hbit)
    (val_colAT hq hc hi) (val_sub (val_const 1 env) (val_bitOfT hcol hi)) ?_)
    (bd_eqT hbi (bd_const (Nat.zero_le _) _) hi (val_const 0 env) ha (Nat.zero_le _) (by omega))
    (val_add (val_colAT hq hc hi) (val_sub (val_const 1 env) (val_bitOfT hcol hi)))
    (val_eqT hi (val_const 0 env)) ?_
  · have e2 : (s.X + 2) * s.W ^ s.g = (s.X + 1) * s.W ^ s.g + s.W ^ s.g := by ring
    omega
  · have e2 : (s.X + 2) * s.W ^ s.g = (s.X + 1) * s.W ^ s.g + s.W ^ s.g := by ring
    split_ifs <;> omega

theorem colZ_le (H X E W r g : ℕ) (res : ℕ → ℕ) (i : ℕ) :
    colZ H X E W r g res i ≤ (X + 1) * W ^ g + 2 := by
  unfold colZ
  have := colA_le H X E W r g res i
  split_ifs <;> omega

theorem bd_outT (hq : Prog'.closed 3 q = true) (hc : c.Good w s env) (hcb : c.GoodB w M env)
    (hs : Sizes s M) (hR : ResOK w q s M) {k : Term}
    (hk : Val w k env (kq s.H s.X s.E s.W (resOf w q s))) (hbk : Bd w M k env) {j : Term}
    {a : ℕ} (hj : Val w j env a) (hbj : Bd w M j env) : Bd w M (outT q c k j) env := by
  have h4 := hs.four_le
  have hJ := hs.gW_le
  refine bd_ite (bd_lt hbj (bd_mul (bd_add hcb.2.2.2.2.2.2.2.1 (bd_const (by omega) _)
    hc.2.2.2.2.2.2.2.1 (val_const 1 _) (by have := hs.g_le; nlinarith [hs.hW]))
    hcb.2.2.2.2.2.1 (val_add hc.2.2.2.2.2.2.2.1 (val_const 1 env)) hc.2.2.2.2.2.1 hJ))
    (val_lt hj (val_mul (val_add hc.2.2.2.2.2.2.2.1 (val_const 1 env)) hc.2.2.2.2.2.1))
    (fun hpos => ?_) fun _ => bd_const (Nat.zero_le _) _
  have haJ : a < (s.g + 1) * s.W := by by_contra h; simp [h] at hpos
  have hcol : FVal w (colZT q c k) env (colZ s.H s.X s.E s.W s.r s.g (resOf w q s)) :=
    fun pre u b hu => val_colZT hq (hc.ext pre) (hk.ext pre) hu
  have hD := hs.chain_bound
  refine bd_bitOfT hcol hj hbj (by omega) (D := (s.X + 2) * s.W ^ s.g + 2)
    (fun b _ => (colZ_le _ _ _ _ _ _ _ _).trans (by nlinarith [hs.one_le_Wg])) hD (by omega)
    fun pre u b hb hu hbu => bd_colZT hq (hc.ext pre) (hcb.ext pre) hs hR (hk.ext pre)
      (hbk.ext pre) hu hbu (by omega)

/-! ### The program -/

/-- `x / 2^i` by repeated halving. -/
def halvesT (x i : Term) : Term := foldT i x fun acc _ => div acc (const 2)

theorem foldl_halves (x i : ℕ) :
    (List.range i).foldl (fun acc _ => acc / 2) x = x / 2 ^ i := by
  induction i with
  | zero => simp
  | succ i ih => rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih,
      Nat.div_div_eq_div_mul, pow_succ]

theorem val_halvesT {x i : Term} {a b : ℕ} (hx : Val w x env a) (hi : Val w i env b) :
    Val w (halvesT x i) env (a / 2 ^ b) := by
  have := val_foldT hi hx (fun acc _ => acc / 2) fun pre u u' p k hu _ =>
    val_div hu (val_const 2 _)
  rwa [foldl_halves] at this

/-- The bit length `⌊log₂ x⌋ + 1` of `x ≥ 1`: the number of `i ≤ x` with `2^i ≤ x`. -/
def bitLenT (x : Term) : Term := sumT (add x (const 1)) fun i => lt (const 0) (halvesT x i)

theorem bitLen_eq {x : ℕ} (hx : 1 ≤ x) :
    ∑ i ∈ range (x + 1), (if 0 < x / 2 ^ i then 1 else 0) = Nat.log 2 x + 1 := by
  have h : ∀ i, (0 < x / 2 ^ i ↔ i < Nat.log 2 x + 1) := fun i => by
    rw [Nat.div_pos_iff, Nat.lt_succ_iff, Nat.le_log_iff_pow_le (by norm_num) (by omega)]
    exact ⟨fun h => h.2, fun h => ⟨Nat.two_pow_pos _, h⟩⟩
  simp only [h]
  rw [sum_boole]
  have hl : Nat.log 2 x + 1 ≤ x + 1 := by have := Nat.log_le_self 2 x; omega
  have : (range (x + 1)).filter (· ≤ Nat.log 2 x) = range (Nat.log 2 x + 1) := by
    ext i; simp only [mem_filter, mem_range]; omega
  simp only [Nat.lt_succ_iff] at *
  rw [this, card_range]; rfl

theorem val_bitLenT {x : Term} {a : ℕ} (hx : Val w x env a) (ha : 1 ≤ a) :
    Val w (bitLenT x) env (Nat.log 2 a + 1) := by
  have := val_sumT (val_add hx (val_const 1 env)) (body := fun i => lt (const 0) (halvesT x i))
    (F := fun i => if 0 < a / 2 ^ i then 1 else 0) fun pre u b hu =>
      val_lt (val_const 0 _) (val_halvesT (hx.ext pre) hu)
  rwa [bitLen_eq ha] at this

theorem bd_bitLenT {x : Term} {a : ℕ} (hx : Val w x env a) (hbx : Bd w M x env) (ha : a + 1 ≤ M) :
    Bd w M (bitLenT x) env := by
  refine bd_sumT (val_add hx (val_const 1 env)) (F := fun i => if 0 < a / 2 ^ i then 1 else 0)
    (fun pre u b hu => val_lt (val_const 0 _) (val_halvesT (hx.ext pre) hu))
    (bd_add hbx (bd_const (by omega) _) hx (val_const 1 _) ha) ha ?_ fun pre u b _ hu hbu => ?_
  · calc _ ≤ ∑ _i ∈ range (a + 1), 1 := sum_le_sum fun i _ => by split_ifs <;> omega
      _ ≤ M := by simp [ha]
  · refine bd_lt (bd_const (Nat.zero_le _) _) ?_
    refine bd_foldT hu (hx.ext pre) (fun acc _ => acc / 2) (fun pre' u u' p k hu _ =>
      val_div hu (val_const 2 _)) hbu (hbx.ext pre) (by omega)
      fun pre' u u' p k _ _ _ _ hbu' _ => bd_div hbu' (bd_const (by omega) _)

/-- The parameter terms, from bound variables. -/
def ctxOf (H X E W r g Wg : Term) : Ctx := ⟨lvl 2, lvl 1, H, X, E, W, r, g, Wg⟩

/-- **The program of the Chinese remainder step**, over `[τ, n, j]`. -/
def bitsT (q Hq Xq Eq Wq : Prog) : Term :=
  letT (call1 Hq (lvl 2)) fun H => letT (call1 Xq (lvl 2)) fun X =>
  letT (call1 Eq (lvl 2)) fun E => letT (call1 Wq (lvl 2)) fun W =>
  letT (div W (bitLenT X)) fun r => letT (add (div E r) (const 1)) fun g =>
  letT (pwT W g) fun Wg =>
  letT (kqT q (ctxOf H X E W r g Wg)) fun k => outT q (ctxOf H X E W r g Wg) k (lvl 0)

/-- The group size `⌊W / (⌊log₂ X⌋ + 1)⌋`. -/
def grpSize (X W : ℕ) : ℕ := W / (Nat.log 2 X + 1)

/-- The number of groups `E / r + 1`. -/
def numGroups (X E W : ℕ) : ℕ := E / grpSize X W + 1

theorem pow_grpSize_lt {X W : ℕ} (hX : 1 ≤ X) (hpos : 1 ≤ grpSize X W) :
    X ^ grpSize X W < 2 ^ W := by
  have h1 : X < 2 ^ (Nat.log 2 X + 1) := Nat.lt_pow_succ_log_self (by norm_num) X
  calc X ^ grpSize X W < (2 ^ (Nat.log 2 X + 1)) ^ grpSize X W :=
        Nat.pow_lt_pow_left h1 (by omega)
    _ = 2 ^ ((Nat.log 2 X + 1) * grpSize X W) := by rw [← pow_mul]
    _ ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) (Nat.mul_div_le W _)

/-- **The Chinese remainder step, elementary version.** For programs `Hq, Xq, Eq, Wq` closed over
`[τ]` and a residue program `q` closed over `[τ, n, p]` there is a program `P` closed over
`[τ, n, j]` such that: if the window `(H, X]` has prime product above `2^(E+1)` with `H ≥ 2`,
`0 ≤ Z ≤ 2^E`, and `q` gives the residues of `Z` at the primes of the window with values at most
`M`, then `P` computes bit `j` of `Z` for every `j`, with values at most `M`, provided `2 ≤ W`,
`X + 1 ≤ 2^(W-1)`, `E + 1 ≤ M` and `4 (X + 1) 2^W (W^g + 1) ≤ M` for `g = numGroups X E W`. -/
theorem exists_bitsProg (q Hq Xq Eq Wq : Prog) (hq : Prog'.closed 3 q = true)
    (hH : Prog'.closed 1 Hq = true) (hX : Prog'.closed 1 Xq = true)
    (hE : Prog'.closed 1 Eq = true) (hW : Prog'.closed 1 Wq = true) :
    ∃ P : Prog, Prog'.closed 3 P = true ∧
      ∀ (w : List Bool) (τ n Z M : ℕ),
        let H := Hq.eval w [τ]
        let X := Xq.eval w [τ]
        let E := Eq.eval w [τ]
        let W := Wq.eval w [τ]
        2 ≤ H → 2 ^ (E + 1) < ∏ p ∈ (Ioc H X).filter Nat.Prime, p → Z ≤ 2 ^ E →
        (∀ p, p.Prime → H < p → p ≤ X →
          q.eval w [τ, n, p] = Z % p ∧ q.Bounded w M [τ, n, p]) →
        Hq.Bounded w M [τ] → Xq.Bounded w M [τ] → Eq.Bounded w M [τ] → Wq.Bounded w M [τ] →
        2 ≤ W → X + 1 ≤ 2 ^ (W - 1) → E + 1 ≤ M →
        4 * ((X + 1) * 2 ^ W * (W ^ numGroups X E W + 1)) ≤ M →
        ∀ j, P.eval w [τ, n, j] = Z / 2 ^ j % 2 ∧ P.Bounded w M [τ, n, j] := by
  refine ⟨closeAt 3 (bitsT q Hq Xq Eq Wq 3), closed_closeAt 3 _, ?_⟩
  intro w τ n Z M H X E W h2H hprod hZ hres hbH hbX hbE hbW hW2 hK hEM hM j
  set env : List ℕ := [τ, n, j]
  have hX1 : 1 ≤ X := by
    by_contra h0
    have : (Ioc H X).filter Nat.Prime = ∅ := by
      ext p; simp only [mem_filter, mem_Ioc]; constructor
      · rintro ⟨⟨h1, h2⟩, -⟩; omega
      · simp
    rw [this, prod_empty] at hprod
    exact absurd hprod (by have := Nat.one_le_two_pow (n := E + 1); omega)
  set r := grpSize X W
  set g := numGroups X E W
  set sc : SC := ⟨τ, n, H, X, E, W, r, g⟩
  have hlog : Nat.log 2 X + 1 ≤ W - 1 := by
    have : X < 2 ^ (W - 1) := by omega
    have := (Nat.log_lt_iff_lt_pow (b := 2) (by norm_num) (by omega)).mpr this
    omega
  have hr1 : 1 ≤ r := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  have hs : Sizes sc M :=
    { hW := hW2, hr := hr1, hXr := pow_grpSize_lt hX1 hr1, hK := hK,
      hg := Nat.lt_succ_self _, hE := hEM, hM := hM }
  have hcorrect : ∀ p, sel H X E p → q.eval w [τ, n, p] = Z % p ∧ q.Bounded w M [τ, n, p] :=
    fun p hp => hres p hp.1.2.2 hp.1.1 hp.1.2.1
  have hR : ResOK w q sc M := fun p hp =>
    ⟨(hcorrect p hp).2, by
      show q.eval w [τ, n, p] < p
      rw [(hcorrect p hp).1]; exact Nat.mod_lt _ (sel_prime hp).pos⟩
  -- the values of the program
  have hτ : Val w (lvl 2) env τ := val_lvl (by simp [env])
  have hn : Val w (lvl 1) env n := val_lvl (by simp [env])
  have hj : Val w (lvl 0) env j := val_lvl (by simp [env])
  have hval : Val w (bitsT q Hq Xq Eq Wq) env (out H X E W r g (resOf w q sc) j) := by
    refine val_letT (val_call1 hH hτ) fun p1 H' hH' => ?_
    refine val_letT (val_call1 hX (hτ.ext p1)) fun p2 X' hX' => ?_
    refine val_letT (val_call1 hE ((hτ.ext p1).ext p2)) fun p3 E' hE' => ?_
    refine val_letT (val_call1 hW (((hτ.ext p1).ext p2).ext p3)) fun p4 W' hW' => ?_
    refine val_letT (val_div hW' (val_bitLenT (((hX'.ext p3).ext p4)) hX1)) fun p5 r' hr' => ?_
    refine val_letT (val_add (val_div ((hE'.ext p4).ext p5) hr') (val_const 1 _))
      fun p6 g' hg' => ?_
    refine val_letT (val_pwT ((hW'.ext p5).ext p6) hg') fun p7 Wg' hWg' => ?_
    have hc : (ctxOf H' X' E' W' r' g' Wg').Good w sc (p7 ++ (p6 ++ (p5 ++ (p4 ++ (p3 ++
        (p2 ++ (p1 ++ env))))))) :=
      ⟨(((((((hτ.ext p1).ext p2).ext p3).ext p4).ext p5).ext p6).ext p7),
        (((((((hn.ext p1).ext p2).ext p3).ext p4).ext p5).ext p6).ext p7),
        ((((((hH'.ext p2).ext p3).ext p4).ext p5).ext p6).ext p7),
        (((((hX'.ext p3).ext p4).ext p5).ext p6).ext p7),
        ((((hE'.ext p4).ext p5).ext p6).ext p7), (((hW'.ext p5).ext p6).ext p7),
        ((hr'.ext p6).ext p7), hg'.ext p7, hWg'⟩
    refine val_letT (val_kqT hq hc) fun p8 k' hk' => ?_
    exact val_outT hq (hc.ext p8) hk' (((((((((hj.ext p1).ext p2).ext p3).ext p4).ext p5).ext
      p6).ext p7).ext p8))
  -- the bounds of the program
  have hbd : Bd w M (bitsT q Hq Xq Eq Wq) env := by
    have h4 := hs.four_le
    have hbτ : Bd w M (lvl 2) env := bd_lvl _ _
    refine bd_letT (val_call1 hH hτ) (bd_call1 hH hτ hbτ hbH) fun p1 H' hH' hbH' => ?_
    refine bd_letT (val_call1 hX (hτ.ext p1)) (bd_call1 hX (hτ.ext p1) (hbτ.ext p1) hbX)
      fun p2 X' hX' hbX' => ?_
    refine bd_letT (val_call1 hE ((hτ.ext p1).ext p2))
      (bd_call1 hE ((hτ.ext p1).ext p2) ((hbτ.ext p1).ext p2) hbE) fun p3 E' hE' hbE' => ?_
    refine bd_letT (val_call1 hW (((hτ.ext p1).ext p2).ext p3))
      (bd_call1 hW (((hτ.ext p1).ext p2).ext p3) (((hbτ.ext p1).ext p2).ext p3) hbW)
      fun p4 W' hW' hbW' => ?_
    refine bd_letT (val_div hW' (val_bitLenT (((hX'.ext p3).ext p4)) hX1))
      (bd_div hbW' (bd_bitLenT ((hX'.ext p3).ext p4) ((hbX'.ext p3).ext p4) hs.X1_le))
      fun p5 r' hr' hbr' => ?_
    have hEr : E / r + 1 ≤ M := by have := Nat.div_le_self E r; omega
    refine bd_letT (val_add (val_div ((hE'.ext p4).ext p5) hr') (val_const 1 _))
      (bd_add (bd_div ((hbE'.ext p4).ext p5) hbr') (bd_const (by omega) _)
        (val_div ((hE'.ext p4).ext p5) hr') (val_const 1 _) hEr) fun p6 g' hg' hbg' => ?_
    refine bd_letT (val_pwT ((hW'.ext p5).ext p6) hg')
      (bd_pwT ((hW'.ext p5).ext p6) hg' ((hbW'.ext p5).ext p6) hbg' le_rfl hs.Wg_le (by omega)
        hs.g_le) fun p7 Wg' hWg' hbWg' => ?_
    have hc : (ctxOf H' X' E' W' r' g' Wg').Good w sc (p7 ++ (p6 ++ (p5 ++ (p4 ++ (p3 ++
        (p2 ++ (p1 ++ env))))))) :=
      ⟨(((((((hτ.ext p1).ext p2).ext p3).ext p4).ext p5).ext p6).ext p7),
        (((((((hn.ext p1).ext p2).ext p3).ext p4).ext p5).ext p6).ext p7),
        ((((((hH'.ext p2).ext p3).ext p4).ext p5).ext p6).ext p7),
        (((((hX'.ext p3).ext p4).ext p5).ext p6).ext p7),
        ((((hE'.ext p4).ext p5).ext p6).ext p7), (((hW'.ext p5).ext p6).ext p7),
        ((hr'.ext p6).ext p7), hg'.ext p7, hWg'⟩
    have hcb : (ctxOf H' X' E' W' r' g' Wg').GoodB w M (p7 ++ (p6 ++ (p5 ++ (p4 ++ (p3 ++
        (p2 ++ (p1 ++ env))))))) :=
      ⟨bd_lvl _ _, bd_lvl _ _, ((((((hbH'.ext p2).ext p3).ext p4).ext p5).ext p6).ext p7),
        (((((hbX'.ext p3).ext p4).ext p5).ext p6).ext p7),
        ((((hbE'.ext p4).ext p5).ext p6).ext p7), (((hbW'.ext p5).ext p6).ext p7),
        ((hbr'.ext p6).ext p7), hbg'.ext p7, hbWg'⟩
    refine bd_letT (val_kqT hq hc) (bd_kqT hq hc hcb hs hR) fun p8 k' hk' hbk' => ?_
    exact bd_outT hq (hc.ext p8) (hcb.ext p8) hs hR hk' hbk'
      (((((((((hj.ext p1).ext p2).ext p3).ext p4).ext p5).ext p6).ext p7).ext p8)) (bd_lvl _ _)
  have hlen : env.length = 3 := rfl
  refine ⟨?_, ?_⟩
  · rw [eval_closeAt _ 3 env hlen]
    have : (bitsT q Hq Xq Eq Wq).denote w env = _ := hval.eq
    refine this.trans (out_eq h2H (by omega) hr1 (pow_grpSize_lt hX1 hr1) hK (Nat.lt_succ_self _)
      hZ hprod (fun p hp hHp hpX => (hres p hp hHp hpX).1) j)
  · rw [bounded_closeAt _ 3 env hlen]
    exact hbd.bnd

end Cslib.Complexity.NtimeDspace.Cross.Exact
