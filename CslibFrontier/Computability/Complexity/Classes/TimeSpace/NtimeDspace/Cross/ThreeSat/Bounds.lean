/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.ThreeSat.Terms

/-!
# The accessors of the 3-SAT network use `O(log s)` bits

For every input word `w` and size `s`, every value arising in the evaluation of the accessor
terms of
`CslibFrontier/Computability/Complexity/Classes/TimeSpace/NtimeDspace/Cross/ThreeSat/Access.lean` is
at most `M` whenever `M ≥ 64 (s + 2)^4`, on arguments in range
(edges `i < 6m`, vertices `v < 7m`, ports `j < 3`, bits `A < 8`, where `m ≤ s`). The decoding reads
at most `(s + 2)^2 + 1` positions, slot indices stay below `22 (s + 2)`, and slot values below
`4 (s + 2)^2 + 6`.
-/

public section

namespace Cslib.Complexity.NtimeDspace.Cross.ThreeSat

open NtimeDspace.ProgLang NtimeDspace.ProgTerm Term NtimeDspace.Cross.Exact Finset

variable {w : List Bool} {M : ℕ} {env : List ℕ}

/-! ### Sizes of the decoded quantities -/

theorem firstNat_le (N : ℕ) (p : ℕ → Bool) : TermBlocks.firstNat N p N ≤ N := by
  rcases (TermBlocks.firstNat_spec N p N le_rfl).2.1 with h | h <;> omega

theorem lastNat_le {d k : ℕ} (p : ℕ → Bool) (hk : k ≤ d) : lastNat d k p ≤ d := by
  rcases lastNat_spec d k p with ⟨h, -⟩ | ⟨h, -⟩ <;> omega

section Sizes

variable (w : List Bool) (s : ℕ)

theorem lenW_le : lenW w s ≤ (s + 2) ^ 2 + 1 := firstNat_le _ _
theorem offW_le : offW w s ≤ lenW w s +
    1 := by unfold offW; have := firstNat_le (lenW w s) (fun i => i % 2 == 0 && ib w i != 1); omega
theorem nW_le : nW w s ≤ lenW w s := by
  unfold nW
  have := firstNat_le (lenW w s - offW w s) (fun k => ib w (offW w s + k) != 1)
  omega

theorem log_two_mul_add_one_le (n : ℕ) : Nat.log 2 (2 * n + 1) ≤ n := by
  have : 2 * n + 1 < 2 ^ (n + 1) := by
    have := Nat.lt_two_pow_self (n := n); rw [pow_succ]; omega
  have := Nat.log_lt_of_lt_pow (by omega) this
  omega

theorem widW_le : widW w s ≤ nW w s + 1 := by
  unfold widW; have := log_two_mul_add_one_le (nW w s); omega

theorem two_pow_widW : 2 ^ widW w s ≤ 4 * nW w s + 2 := by
  unfold widW
  have := Nat.pow_log_le_self 2 (show 2 * nW w s + 1 ≠ 0 by omega)
  rw [pow_succ]; omega

theorem svW_lt (t : ℕ) : svW w s t < 2 ^ widW w s := TermBlocks.bitsNum_lt _ _

theorem mW_le' : (rawW w s).m ≤ s := mW_le w s

end Sizes

/-! ### Decoding -/

section Decoding

variable {sT : Term} {s : ℕ}

theorem bd_eqT' {a b : Term} {x y : ℕ} (ha : Bd w M a env) (hb : Bd w M b env) (hva : Val w a env x)
    (hvb : Val w b env y) (hx : x ≤ M) (hy : y ≤ M) (h1 : 1 ≤ M) : Bd w M (Exact.eqT a b) env :=
  bd_eqT ha hb hva hvb hx hy h1

/-- The standing size hypothesis. -/
structure Sz (s M : ℕ) : Prop where
  hM : 64 * (s + 2) ^ 4 ≤ M

theorem Sz.q2 {s M : ℕ} (_ : Sz s M) : 4 ≤ (s + 2) ^ 2 :=
  (Nat.pow_le_pow_left (show 2 ≤ s + 2 by omega) 2).trans' (by norm_num)

theorem Sz.le {s M : ℕ} (h : Sz s M) : 64 * ((s + 2) ^ 2) ^ 2 ≤ M := by
  have := h.hM; rw [← pow_mul] at *; simpa using this

theorem Sz.lin {s M : ℕ} (h : Sz s M) : 64 * (s + 2) ^ 2 ≤ M := by
  have h1 := h.le; have h2 := h.q2
  nlinarith

theorem Sz.s_le {s M : ℕ} (_h : Sz s M) : s + 2 ≤ (s + 2) ^ 2 := by nlinarith

theorem fv_len : FValB w (fun i => Exact.eqT (input i) (const 2)) env (fun i => ib w i == 2) :=
  fun pre u q hu => by
    have := val_eqT (val_input hu) (val_const 2 (pre ++ env)); rwa [eqT_toNat] at this

theorem fv_off : FValB w (fun i => mul (Exact.eqT (mod i (const 2)) (const 0))
    (sub (const 1) (Exact.eqT (input i) (const 1)))) env (fun i => i % 2 == 0 && ib w i != 1) :=
  fun pre u q hu => by
    have := val_mul (val_eqT (val_mod hu (val_const 2 _)) (val_const 0 _))
      (val_sub (val_const 1 _) (val_eqT (val_input hu) (val_const 1 _)))
    refine fun extra => (this extra).trans ?_
    symm; by_cases h1 : q % 2 = 0 <;> by_cases h2 : ib w q = 1 <;> simp [h1, h2]

theorem fv_n (hs : Val w sT env s) : FValB w (fun k => sub (const 1)
    (Exact.eqT (input (add (offT sT) k)) (const 1))) env (fun k => ib w (offW w s + k) != 1) :=
  fun pre u q hu => by
    have := val_sub (val_const 1 _) (val_eqT (val_input (val_add ((val_offT hs).ext pre) hu))
      (val_const 1 _))
    refine fun extra => (this extra).trans ?_
    symm; by_cases h : ib w (offW w s + q) = 1 <;> simp [h]

theorem bd_bndT (hs : Val w sT env s) (hbs : Bd w M sT env) (hz : Sz s M) :
    Bd w M (bndT sT) env := by
  have h1 := hz.lin; have h2 := hz.s_le
  refine bd_mul (bd_add hbs (bd_const (by omega) _) hs (val_const 2 env) (by omega))
    (bd_add hbs (bd_const (by omega) _) hs (val_const 2 env) (by omega))
    (val_add hs (val_const 2 env)) (val_add hs (val_const 2 env)) ?_
  nlinarith

theorem bd_lenT (hs : Val w sT env s) (hbs : Bd w M sT env) (hz : Sz s M) :
    Bd w M (lenT sT) env := by
  have h1 := hz.lin; have h2 := hz.s_le
  have hv := val_add (val_bndT hs) (val_const 1 env)
  refine bd_findT hv (bd_add (bd_bndT hs hbs hz) (bd_const (by omega) _) (val_bndT hs)
      (val_const 1 env)
    (by rw [bnd]; omega)) (by rw [bnd]; omega) fv_len fun pre u q _ hu hbu => ?_
  · have hib : ib w q ≤ 2 := by unfold ib ProgLang.Prog.inputValue; split <;> omega
    exact bd_eqT (bd_input hbu) (bd_const (by omega) _) (val_input hu) (val_const 2 _) (by omega)
      (by omega) (by omega)

theorem bd_offT (hs : Val w sT env s) (hbs : Bd w M sT env) (hz : Sz s M) :
    Bd w M (offT sT) env := by
  have h1 := hz.lin; have h2 := hz.s_le
  have hl := lenW_le w s
  refine bd_add (bd_findT (val_lenT hs) (bd_lenT hs hbs hz) (by omega) fv_off
    fun pre u q _ hu hbu => ?_) (bd_const (by omega) _) (val_findT (val_lenT hs) fv_off)
    (val_const 1 env) ?_
  · have hib : ib w q ≤ 2 := by unfold ib ProgLang.Prog.inputValue; split <;> omega
    refine bd_mul (bd_eqT (bd_mod hbu (bd_const (by omega) _)) (bd_const (by omega) _)
      (val_mod hu (val_const 2 _)) (val_const 0 _) (by omega) (by omega) (by omega))
      (bd_sub (bd_const (by omega) _) (bd_eqT (bd_input hbu) (bd_const (by omega) _) (val_input hu)
        (val_const 1 _) (by omega) (by omega) (by omega)))
      (val_eqT (val_mod hu (val_const 2 _)) (val_const 0 _))
      (val_sub (val_const 1 _) (val_eqT (val_input hu) (val_const 1 _))) ?_
    split_ifs <;> omega
  · have := offW_le w s; unfold offW at this; omega

theorem bd_nT (hs : Val w sT env s) (hbs : Bd w M sT env) (hz : Sz s M) :
    Bd w M (nT sT) env := by
  have h1 := hz.lin; have h2 := hz.s_le
  have hl := lenW_le w s; have ho := offW_le w s
  refine bd_findT (val_sub (val_lenT hs) (val_offT hs))
      (bd_sub (bd_lenT hs hbs hz) (bd_offT hs hbs hz))
    (by omega) (fv_n hs) fun pre u q hq hu hbu => ?_
  · have hib : ib w (offW w s + q) ≤ 2 := by unfold ib ProgLang.Prog.inputValue; split <;> omega
    exact bd_sub (bd_const (by omega) _) (bd_eqT (bd_input (bd_add ((bd_offT hs hbs hz).ext pre) hbu
      ((val_offT hs).ext pre) hu (by omega))) (bd_const (by omega) _)
      (val_input (val_add ((val_offT hs).ext pre) hu)) (val_const 1 _) (by omega)
          (by omega) (by omega))

theorem bd_widT (hs : Val w sT env s) (hbs : Bd w M sT env) (hz : Sz s M) :
    Bd w M (widT sT) env := by
  have h1 := hz.lin; have h2 := hz.s_le
  have hl := lenW_le w s; have hn := nW_le w s
  have hv := val_add (val_mul (val_const 2 env) (val_nT hs)) (val_const 1 env)
  exact bd_bitLenT hv (bd_add (bd_mul (bd_const (by omega) _) (bd_nT hs hbs hz) (val_const 2 env)
    (val_nT hs) (by omega)) (bd_const (by omega) _) (val_mul (val_const 2 env) (val_nT hs))
    (val_const 1 env) (by omega)) (by omega)

theorem bd_mT (hs : Val w sT env s) (hbs : Bd w M sT env) (hz : Sz s M) :
    Bd w M (mT sT) env := by
  have h1 := hz.lin; have h2 := hz.s_le
  have hl := lenW_le w s; have hn := nW_le w s; have hw := widW_le w s
  refine bd_minT' (bd_div (bd_sub (bd_sub (bd_sub (bd_lenT hs hbs hz) (bd_offT hs hbs hz))
    (bd_nT hs hbs hz)) (bd_const (by omega) _)) (bd_mul (bd_const (by omega) _) (bd_widT hs hbs hz)
    (val_const 3 env) (val_widT hs) (by omega))) hbs
    (val_div (val_sub (val_sub (val_sub (val_lenT hs) (val_offT hs)) (val_nT hs)) (val_const 1 env))
      (val_mul (val_const 3 env) (val_widT hs))) hs

theorem bd_svT {tT : Term} {t : ℕ} (hs : Val w sT env s) (hbs : Bd w M sT env) (hz : Sz s M)
    (ht : Val w tT env t) (hbt : Bd w M tT env) (htT : t ≤ 22 * (s + 2)) :
    Bd w M (svT sT tT) env := by
  have h1 := hz.le; have h2 := hz.s_le; have hq := hz.q2
  have hl := lenW_le w s; have hn := nW_le w s; have hw := widW_le w s; have ho := offW_le w s
  have h2w := two_pow_widW w s
  set Q := (s + 2) ^ 2
  have hW : widW w s ≤ Q + 2 := by omega
  have htW : t * widW w s ≤ 22 * Q * (Q + 2) := Nat.mul_le_mul (by nlinarith) hW
  refine bd_ofBitsT (val_widT hs) (bd_widT hs hbs hz) (fun pre u q hu => val_input
    (val_add (val_add (val_add (val_add ((val_offT hs).ext pre) ((val_nT hs).ext pre))
      (val_const 1 _)) (val_mul (ht.ext pre) ((val_widT hs).ext pre))) hu))
    (fun pre u q hq hu hbu => ?_) (by nlinarith) (by nlinarith)
  have hon := bd_add ((bd_offT hs hbs hz).ext pre) ((bd_nT hs hbs hz).ext pre)
      ((val_offT hs).ext pre)
    ((val_nT hs).ext pre) (by nlinarith)
  have hon1 := bd_add hon (bd_const (by nlinarith) _)
      (val_add ((val_offT hs).ext pre) ((val_nT hs).ext pre))
    (val_const 1 _) (by nlinarith)
  have htw := bd_mul (hbt.ext pre) ((bd_widT hs hbs hz).ext pre) (ht.ext pre)
      ((val_widT hs).ext pre)
    (by nlinarith)
  have h3 := bd_add hon1 htw (val_add (val_add ((val_offT hs).ext pre) ((val_nT hs).ext pre))
    (val_const 1 _)) (val_mul (ht.ext pre) ((val_widT hs).ext pre)) (by nlinarith)
  exact bd_input (bd_add h3 hbu (val_add
      (val_add (val_add ((val_offT hs).ext pre) ((val_nT hs).ext pre))
      (val_const 1 _)) (val_mul (ht.ext pre) ((val_widT hs).ext pre))) hu (by nlinarith))

end Decoding

end Cslib.Complexity.NtimeDspace.Cross.ThreeSat
