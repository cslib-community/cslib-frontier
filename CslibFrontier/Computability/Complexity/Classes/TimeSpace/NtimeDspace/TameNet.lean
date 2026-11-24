/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.NetSystemTerm
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.TameTac
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.TameV

/-!
# Tiers of the network accessors

`2 ^ arity(e)` is bounded for real vertices `e < m` by a degree bound `D₀ < L`
(`tm_pow2_arityNT`); the letter packing uses `2 ^ r` for `r` below the letter
width (`tm_pow2_letter`). With these and the stable powers as hypotheses,
`tame` bounds the weight term (`tm_weightNT`), the arity and the ports.
-/

public section

namespace Cslib.Complexity.NtimeDspace.ProgTerm

open Term LocalSim _root_.Turing _root_.Turing.MultiTapePTM

variable {w : List Bool} {L : ℕ} {env : List ℕ}

theorem tm_pow2_arityNT {k s : ℕ} {qT bT σT : Term} {mv D0 : ℕ} (hL : 8 ≤ L)
    (hq : Tm w L 1 qT env) (hb : Tm w L 1 bT env) (hσ : Tm w L 1 σT env)
    (hqs : StableAt w qT env) (hbs : StableAt w bT env) (hσs : StableAt w σT env)
    (hdeg : ∀ v < mv, (explicitPortsNum k (qT.denote w env) (letterBits k s (bT.denote w env))
      (σT.denote w env) v).length ≤ D0) (hD0 : D0 < L) (hconst : 4 * k + s + 100 < 2 ^ L) :
    TmFv w L (fun e => pow2 (arityNT k s qT bT σT e)) 4 mv 1 env := by
  intro env' he e1 he1 he1s he1v
  refine t_pow2_lt (de := 8) (V := D0 + 1) ?_ (by omega) (fun pre hp => ?_) (by omega) (by omega)
    (by omega)
  · tame
  · have hext : Ext L (pre ++ env') env := Ext.trans ⟨pre, hp, rfl⟩ he
    rw [denote_arityNT (hqs.extend' hext) (hbs.extend' hext) (hσs.extend' hext) (he1s.extend pre),
      hqs.extend'_eq hext, hbs.extend'_eq hext, hσs.extend'_eq hext]
    exact Nat.lt_succ_of_le (hdeg _ (he1v pre hp))

theorem tm_pow2_letter {m0 : ℕ} (hm0 : m0 < L) (hL : 8 ≤ L) :
    TmFv w L (fun r => powT (const 2) r) 4 m0 1 env := by
  intro env' he r hr hrs hrv
  refine t_powT_lt (tm_const (d := 1) (lit_lt_two_pow (by omega) (by omega)) (by omega))
    (stableAt_const _ _) hr (by omega) hrv (by omega) le_rfl ?_ (by omega) (by omega)
  simp only [denote_const, one_mul]
  exact Nat.pow_lt_pow_right (by norm_num) hm0

end Cslib.Complexity.NtimeDspace.ProgTerm
