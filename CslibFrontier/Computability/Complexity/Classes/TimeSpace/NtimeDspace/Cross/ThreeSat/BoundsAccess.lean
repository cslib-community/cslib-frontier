/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.ThreeSat.Access
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.ThreeSat.Bounds

/-!
# Bounds for the slot functions and the accessors of the 3-SAT network

`bd_*` lemmas for the slot functions (slot indices at most `22 (s + 2)`) and for the accessors
(edges `i < 6m`, vertices `v < 7m`, bits `A < 8`), under `Sz s M`: `M ≥ 64 (s + 2)^4`.
-/

public section

namespace Cslib.Complexity.NtimeDspace.Cross.ThreeSat

open NtimeDspace.ProgLang NtimeDspace.ProgTerm Term NtimeDspace.Cross.Exact Finset

variable {w : List Bool} {M : ℕ} {env : List ℕ}

theorem mul_le_one' {a b : ℕ} (ha : a ≤ 1) (hb : b ≤ 1) : a * b ≤ 1 :=
  (Nat.mul_le_mul ha hb).trans (by norm_num)

section Slots

variable {sT tT t'T : Term} {s t t' : ℕ}

theorem Sz.facts {s M : ℕ} (hz : Sz s M) : 64 * (s + 2) ^ 2 ≤ M ∧ 4 ≤ (s + 2) ^ 2 ∧
    s + 2 ≤ (s + 2) ^ 2 := ⟨hz.lin, hz.q2, hz.s_le⟩

theorem rawW_m_le (w : List Bool) (s : ℕ) : (rawW w s).m ≤ s := mW_le w s

theorem svW_le_M (hz : Sz s M) : svW w s t ≤ M := by
  have h1 := svW_lt w s t; have h2 := two_pow_widW w s; have h3 := nW_le w s
  have h4 := lenW_le w s; obtain ⟨h5, h6, h7⟩ := hz.facts
  omega

theorem sv_le_M (hz : Sz s M) : (rawW w s).sv t ≤ M := by dsimp only [rawW]; exact svW_le_M hz

theorem fv_same (hs : Val w sT env s) (ht : Val w tT env t) :
    FValB w (fun i => sameT sT tT i) env ((rawW w s).same t) :=
  fun pre _u _q hu => val_sameT (hs.ext pre) (ht.ext pre) hu

theorem fv_next (hs : Val w sT env s) (ht : Val w tT env t) :
    FValB w (fun t' => mul (lt tT t') (sameT sT tT t')) env
      (fun t' => decide (t < t') && (rawW w s).same t t') := fun pre u q hu => by
  have := val_mul (val_lt (ht.ext pre) hu) (val_sameT (hs.ext pre) (ht.ext pre) hu)
  refine fun extra => (this extra).trans ?_
  symm; by_cases h : t < q <;> simp [h]

variable (hs : Val w sT env s) (hbs : Bd w M sT env) (hz : Sz s M)
include hs hbs hz

theorem bd_presT (ht : Val w tT env t) (hbt : Bd w M tT env) (htT : t ≤ 22 * (s + 2)) :
    Bd w M (presT sT tT) env :=
  bd_lt (bd_const (Nat.zero_le _) _) (bd_svT hs hbs hz ht hbt htT)

theorem bd_varT (ht : Val w tT env t) (hbt : Bd w M tT env) (htT : t ≤ 22 * (s + 2)) :
    Bd w M (varT sT tT) env :=
  bd_div (bd_sub (bd_svT hs hbs hz ht hbt htT)
      (bd_const (by obtain ⟨_, _, _⟩ := hz.facts; omega) _))
    (bd_const (by obtain ⟨_, _, _⟩ := hz.facts; omega) _)

theorem bd_signT (ht : Val w tT env t) (hbt : Bd w M tT env) (htT : t ≤ 22 * (s + 2)) :
    Bd w M (signT sT tT) env :=
  bd_mod (bd_sub (bd_svT hs hbs hz ht hbt htT)
      (bd_const (by obtain ⟨_, _, _⟩ := hz.facts; omega) _))
    (bd_const (by obtain ⟨_, _, _⟩ := hz.facts; omega) _)

theorem bd_sameT (ht : Val w tT env t) (hbt : Bd w M tT env) (htT : t ≤ 22 * (s + 2))
    (ht' : Val w t'T env t') (hbt' : Bd w M t'T env) (htT' : t' ≤ 22 * (s + 2)) :
    Bd w M (sameT sT tT t'T) env := by
  obtain ⟨hl, hq2, hsq⟩ := hz.facts
  have hs1 : (rawW w s).sv t ≤ M := sv_le_M hz
  have hs2 : (rawW w s).sv t' ≤ M := sv_le_M hz
  have hv1 : (rawW w s).var t ≤ M := by unfold Raw.var; omega
  have hv2 : (rawW w s).var t' ≤ M := by unfold Raw.var; omega
  refine bd_mul (bd_presT hs hbs hz ht' hbt' htT') (bd_eqT (bd_varT hs hbs hz ht' hbt' htT')
    (bd_varT hs hbs hz ht hbt htT) (val_varT hs ht') (val_varT hs ht) hv2 hv1 (by omega))
    (val_presT hs ht') (val_eqT (val_varT hs ht') (val_varT hs ht)) ?_
  have := Bool.toNat_le ((rawW w s).pres t')
  split_ifs <;> omega

theorem bd_m3T : Bd w M (m3T sT) env := by
  obtain ⟨hl, hq2, hsq⟩ := hz.facts; have hm := rawW_m_le w s
  exact bd_mul (bd_const (by omega) _) (bd_mT hs hbs hz) (val_const 3 env) (val_mT hs)
    (by omega)

omit hs hbs in
theorem m3_le : 3 * (rawW w s).m ≤ M := by
  obtain ⟨hl, hq2, hsq⟩ := hz.facts; have hm := rawW_m_le w s
  omega

theorem bd_nextT (ht : Val w tT env t) (hbt : Bd w M tT env) (htT : t ≤ 22 * (s + 2)) :
    Bd w M (nextT sT tT) env := by
  obtain ⟨hl, hq2, hsq⟩ := hz.facts; have hm := rawW_m_le w s
  refine bd_findT (val_m3T hs) (bd_m3T hs hbs hz) (m3_le hz) (fv_next hs ht)
    fun pre u q hq hu hbu => ?_
  have hq' : q ≤ 22 * (s + 2) := by omega
  refine bd_mul (bd_lt (hbt.ext pre) hbu) (bd_sameT (hs.ext pre) (hbs.ext pre) hz (ht.ext pre)
    (hbt.ext pre) htT hu hbu hq') (val_lt (ht.ext pre) hu)
        (val_sameT (hs.ext pre) (ht.ext pre) hu) ?_
  have := Bool.toNat_le ((rawW w s).same t q)
  split_ifs <;> omega

theorem bd_hasNextT (ht : Val w tT env t) (hbt : Bd w M tT env) (htT : t ≤ 22 * (s + 2)) :
    Bd w M (hasNextT sT tT) env := by
  obtain ⟨hl, hq2, hsq⟩ := hz.facts
  refine bd_mul (bd_presT hs hbs hz ht hbt htT) (bd_lt (bd_nextT hs hbs hz ht hbt htT)
    (bd_m3T hs hbs hz)) (val_presT hs ht) (val_lt (val_nextT hs ht) (val_m3T hs)) ?_
  have := Bool.toNat_le ((rawW w s).pres t)
  split_ifs <;> omega

theorem bd_prevT (ht : Val w tT env t) (hbt : Bd w M tT env) (htT : t ≤ 22 * (s + 2)) :
    Bd w M (prevT sT tT) env := by
  obtain ⟨hl, hq2, hsq⟩ := hz.facts
  refine bd_lastT ht hbt ht hbt (by omega) (fv_same hs ht) fun pre u q hq hu hbu => ?_
  exact bd_sameT (hs.ext pre) (hbs.ext pre) hz (ht.ext pre) (hbt.ext pre) htT hu hbu (by omega)

theorem bd_hasPrevT (ht : Val w tT env t) (hbt : Bd w M tT env) (htT : t ≤ 22 * (s + 2)) :
    Bd w M (hasPrevT sT tT) env := by
  obtain ⟨hl, hq2, hsq⟩ := hz.facts
  refine bd_mul (bd_presT hs hbs hz ht hbt htT) (bd_lt (bd_prevT hs hbs hz ht hbt htT) hbt)
    (val_presT hs ht) (val_lt (val_prevT hs ht) ht) ?_
  have := Bool.toNat_le ((rawW w s).pres t)
  split_ifs <;> omega

end Slots

/-! ### The accessors -/

section Accessors

variable {sT iT vT jT AT : Term} {s i v j A : ℕ}
variable (hs : Val w sT env s) (hbs : Bd w M sT env) (hz : Sz s M)
include hs hbs hz

theorem bd_edgesT : Bd w M (edgesT sT) env := by
  obtain ⟨hl, hq2, hsq⟩ := hz.facts; have hm := rawW_m_le w s
  exact bd_mul (bd_const (by omega) _) (bd_mT hs hbs hz) (val_const 6 env) (val_mT hs) (by omega)

theorem bd_vertsT : Bd w M (vertsT sT) env := by
  obtain ⟨hl, hq2, hsq⟩ := hz.facts; have hm := rawW_m_le w s
  exact bd_mul (bd_const (by omega) _) (bd_mT hs hbs hz) (val_const 7 env) (val_mT hs) (by omega)

theorem bd_m4T : Bd w M (m4T sT) env := by
  obtain ⟨hl, hq2, hsq⟩ := hz.facts; have hm := rawW_m_le w s
  exact bd_mul (bd_const (by omega) _) (bd_mT hs hbs hz) (val_const 4 env) (val_mT hs) (by omega)

theorem bd_endUT (hi : Val w iT env i) (hbi : Bd w M iT env) (him : i < 6 * (rawW w s).m) :
    Bd w M (endUT sT iT) env := by
  obtain ⟨hl, hq2, hsq⟩ := hz.facts; have hm := rawW_m_le w s
  refine bd_ite (bd_lt hbi (bd_m3T hs hbs hz)) (val_lt hi (val_m3T hs))
    (fun _ => bd_div hbi (bd_const (by omega) _))
    (fun _ => bd_add (bd_mT hs hbs hz) (bd_sub hbi (bd_m3T hs hbs hz)) (val_mT hs)
      (val_sub hi (val_m3T hs)) (by omega))

theorem bd_endWT (hi : Val w iT env i) (hbi : Bd w M iT env) (him : i < 6 * (rawW w s).m) :
    Bd w M (endWT sT iT) env := by
  obtain ⟨hl, hq2, hsq⟩ := hz.facts; have hm := rawW_m_le w s
  have hj := val_sub hi (val_m3T hs)
  have hbj := bd_sub hbi (bd_m3T hs hbs hz)
  have hjT : i - 3 * (rawW w s).m ≤ 22 * (s + 2) := by omega
  refine bd_ite (bd_lt hbi (bd_m3T hs hbs hz)) (val_lt hi (val_m3T hs))
    (fun _ => bd_add (bd_mT hs hbs hz) hbi (val_mT hs) hi (by omega))
    (fun _ => bd_ite (bd_hasNextT hs hbs hz hj hbj hjT) (val_hasNextT hs hj)
      (fun hn => bd_add (bd_mT hs hbs hz) (bd_nextT hs hbs hz hj hbj hjT) (val_mT hs)
        (val_nextT hs hj) ?_)
      (fun _ => bd_add (bd_m4T hs hbs hz) hbj (val_m4T hs) hj (by omega)))
  have hn' : (rawW w s).hasNext (i - 3 * (rawW w s).m) = true := by simpa using hn
  have := (Raw.next_spec hn').2.1
  omega

theorem bd_degT' (hv : Val w vT env v) (hbv : Bd w M vT env) (hvm : v < 7 * (rawW w s).m) :
    Bd w M (degT' sT vT) env := by
  obtain ⟨hl, hq2, hsq⟩ := hz.facts; have hm := rawW_m_le w s
  have h1 := val_sub hv (val_mT hs); have hb1 := bd_sub hbv (bd_mT hs hbs hz)
  have h4 := val_sub hv (val_m4T hs); have hb4 := bd_sub hbv (bd_m4T hs hbs hz)
  refine bd_ite (bd_lt hbv (bd_mT hs hbs hz)) (val_lt hv (val_mT hs))
    (fun _ => bd_const (by omega) _)
    (fun _ => bd_ite (bd_lt hbv (bd_m4T hs hbs hz)) (val_lt hv (val_m4T hs))
      (fun _ => bd_add (bd_const (by omega) _) (bd_hasPrevT hs hbs hz h1 hb1 (by omega))
        (val_const 2 env) (val_hasPrevT hs h1)
            (by have := Bool.toNat_le ((rawW w s).hasPrev (v - (rawW w s).m)); omega))
      (fun _ => bd_sub (bd_const (by omega) _) (bd_hasNextT hs hbs hz h4 hb4 (by omega))))

theorem bd_portT' (hv : Val w vT env v) (hbv : Bd w M vT env) (hvm : v < 7 * (rawW w s).m)
    (hj : Val w jT env j) (hbj : Bd w M jT env) (hj3 : j ≤ 3) :
    Bd w M (portT' sT vT jT) env := by
  obtain ⟨hl, hq2, hsq⟩ := hz.facts; have hm := rawW_m_le w s
  have h1 := val_sub hv (val_mT hs); have hb1 := bd_sub hbv (bd_mT hs hbs hz)
  have h4 := val_sub hv (val_m4T hs); have hb4 := bd_sub hbv (bd_m4T hs hbs hz)
  have hp : (rawW w s).prev (v - (rawW w s).m) ≤ v - (rawW w s).m := lastNat_le _ le_rfl
  refine bd_ite (bd_lt hbv (bd_mT hs hbs hz)) (val_lt hv (val_mT hs))
    (fun _ => bd_add (bd_mul (bd_const (by omega) _) hbv (val_const 3 env) hv (by omega)) hbj
      (val_mul (val_const 3 env) hv) hj (by omega))
    (fun _ => bd_ite (bd_lt hbv (bd_m4T hs hbs hz)) (val_lt hv (val_m4T hs))
      (fun _ => bd_ite (bd_lt hbj (bd_const (by omega) _)) (val_lt hj (val_const 1 env))
        (fun _ => hb1)
        (fun _ => bd_ite (bd_lt hbj (bd_const (by omega) _)) (val_lt hj (val_const 2 env))
          (fun _ => bd_add (bd_m3T hs hbs hz) hb1 (val_m3T hs) h1 (by omega))
          (fun _ => bd_add (bd_m3T hs hbs hz) (bd_prevT hs hbs hz h1 hb1 (by omega)) (val_m3T hs)
            (val_prevT hs h1) (by omega))))
      (fun _ => bd_add (bd_m3T hs hbs hz) hb4 (val_m3T hs) h4 (by omega)))

omit hs hbs hz in
theorem bd_bitT (hA : Bd w M AT env) (k : ℕ) (hk : k ≤ M) : Bd w M (bit AT (const k)) env :=
  bd_bit hA (bd_const hk _)

theorem bd_funT (hv : Val w vT env v) (hbv : Bd w M vT env) (hvm : v < 7 * (rawW w s).m)
    (hA : Val w AT env A) (hbA : Bd w M AT env) :
    Bd w M (funT sT vT AT) env := by
  obtain ⟨hl, hq2, hsq⟩ := hz.facts; have hm := rawW_m_le w s
  have h1M : 3 ≤ M := by omega
  have h1 := val_sub hv (val_mT hs); have hb1 := bd_sub hbv (bd_mT hs hbs hz)
  have h4 := val_sub hv (val_m4T hs); have hb4 := bd_sub hbv (bd_m4T hs hbs hz)
  have hb := fun k (hk : k ≤ 2) => bd_bitT hbA k (by omega)
  have hbv' := fun k => val_bitT hA (env := env) k
  have tl := fun (b : Bool) => Bool.toNat_le b
  refine bd_ite (bd_lt hbv (bd_mT hs hbs hz)) (val_lt hv (val_mT hs)) (fun hc => ?_) (fun _ => ?_)
  · -- the clause
    have hcm : v < (rawW w s).m := by simpa using hc
    have hsl : ∀ k : ℕ, k ≤ 2 → Val w (add (mul (const 3) vT) (const k)) env (3 * v + k) ∧
        Bd w M (add (mul (const 3) vT) (const k)) env ∧ 3 * v + k ≤ 22 * (s + 2) := fun k hk =>
      ⟨val_add (val_mul (val_const 3 env) hv) (val_const k env),
        bd_add (bd_mul (bd_const (by omega) _) hbv (val_const 3 env) hv (by omega))
          (bd_const (by omega) _) (val_mul (val_const 3 env) hv) (val_const k env) (by omega),
        by omega⟩
    have hp := fun k (hk : k ≤ 2) => bd_presT hs hbs hz (hsl k hk).1 (hsl k hk).2.1 (hsl k hk).2.2
    have hpv := fun k (hk : k ≤ 2) => val_presT hs (hsl k hk).1
    have hsg := fun k (hk : k ≤ 2) => bd_signT hs hbs hz (hsl k hk).1 (hsl k hk).2.1 (hsl k hk).2.2
    have hsgv := fun k (hk : k ≤ 2) => val_signT hs (hsl k hk).1
    have himp := fun k (hk : k ≤ 2) => bd_sub (bd_const (k := 1) (by omega) _) (bd_mul (bd_sub
      (bd_const (k := 1) (by omega) _) (hp k hk)) (hb k hk)
          (val_sub (val_const 1 env) (hpv k hk)) (hbv' k)
      ((mul_le_one' (by omega) (tl _)).trans (by omega)))
    have himpv := fun k (hk : k ≤ 2) => val_impT (hpv k hk) (hbv' k)
    have hhit := fun k (hk : k ≤ 2) => bd_mul (hp k hk) (bd_eqT (hb k hk) (hsg k hk) (hbv' k)
      (hsgv k hk) (by have := tl ((A.testBit k)); omega)
      (by have := tl ((rawW w s).sign (3 * v + k)); omega) (by omega)) (hpv k hk)
      (val_eqT (hbv' k) (hsgv k hk))
      (by have := tl ((rawW w s).pres (3 * v + k)); split_ifs <;> omega)
    have hhitv := fun k (hk : k ≤ 2) => val_hitT (hpv k hk) (hbv' k) (hsgv k hk)
    refine bd_mul (bd_mul (himp 0 (by omega)) (bd_mul (himp 1 (by omega)) (himp 2 (by omega))
        (himpv 1 (by omega)) (himpv 2 (by omega)) ?_) (himpv 0 (by omega))
        (val_mul (himpv 1 (by omega)) (himpv 2 (by omega))) ?_)
      (bd_lt (bd_const (by omega) _) (bd_add (hhit 0 (by omega)) (bd_add (hhit 1 (by omega))
        (hhit 2 (by omega)) (hhitv 1 (by omega)) (hhitv 2 (by omega)) ?_) (hhitv 0 (by omega))
        (val_add (hhitv 1 (by omega)) (hhitv 2 (by omega))) ?_))
      (val_mul (himpv 0 (by omega)) (val_mul (himpv 1 (by omega)) (himpv 2 (by omega))))
      (val_lt (val_const 0 env) (val_add (hhitv 0 (by omega)) (val_add (hhitv 1 (by omega))
        (hhitv 2 (by omega))))) ?_
    · exact (mul_le_one' (tl _) (tl _)).trans (by omega)
    · exact (mul_le_one' (tl _) (mul_le_one' (tl _) (tl _))).trans (by omega)
    · exact (Nat.add_le_add (tl _) (tl _)).trans (by omega)
    · exact (Nat.add_le_add (tl _) (Nat.add_le_add (tl _) (tl _))).trans (by omega)
    · exact (mul_le_one' (mul_le_one' (tl _) (mul_le_one' (tl _) (tl _)))
        (by split_ifs <;> omega)).trans (by omega)
  · refine bd_ite (bd_lt hbv (bd_m4T hs hbs hz)) (val_lt hv (val_m4T hs))
      (fun _ => ?_) (fun _ => ?_)
    · -- an occurrence
      have hnx := bd_hasNextT hs hbs hz h1 hb1 (by omega)
      have hpr := bd_hasPrevT hs hbs hz h1 hb1 (by omega)
      have e1 := bd_eqT (hb 0 (by omega)) (hb 1 (by omega)) (hbv' 0) (hbv' 1)
        (by have := tl (A.testBit 0); omega) (by have := tl (A.testBit 1); omega) (by omega)
      have e2 := bd_eqT (hb 0 (by omega)) (hb 2 (by omega)) (hbv' 0) (hbv' 2)
        (by have := tl (A.testBit 0); omega) (by have := tl (A.testBit 2); omega) (by omega)
      refine bd_mul (bd_sub (bd_const (by omega) _) (bd_mul hnx (bd_sub (bd_const (by omega) _) e1)
          (val_hasNextT hs h1) (val_sub (val_const 1 env) (val_eqT (hbv' 0) (hbv' 1))) ?_))
        (bd_sub (bd_const (by omega) _) (bd_mul hpr (bd_sub (bd_const (by omega) _) e2)
          (val_hasPrevT hs h1) (val_sub (val_const 1 env) (val_eqT (hbv' 0) (hbv' 2))) ?_))
        (val_sub (val_const 1 env) (val_mul (val_hasNextT hs h1)
          (val_sub (val_const 1 env) (val_eqT (hbv' 0) (hbv' 1)))))
        (val_sub (val_const 1 env) (val_mul (val_hasPrevT hs h1)
          (val_sub (val_const 1 env) (val_eqT (hbv' 0) (hbv' 2))))) ?_
      · exact (mul_le_one' (tl _) (by split_ifs <;> omega)).trans (by omega)
      · exact (mul_le_one' (tl _) (by split_ifs <;> omega)).trans (by omega)
      · exact (mul_le_one' (by omega) (by omega)).trans (by omega)
    · -- a sink
      have hnx := bd_hasNextT hs hbs hz h4 hb4 (by omega)
      exact bd_sub (bd_const (by omega) _)
          (bd_mul (bd_sub (bd_const (by omega) _) hnx) (hb 0 (by omega))
        (val_sub (val_const 1 env) (val_hasNextT hs h4)) (hbv' 0)
        ((mul_le_one' (by omega) (tl _)).trans (by omega)))

end Accessors

end Cslib.Complexity.NtimeDspace.Cross.ThreeSat
