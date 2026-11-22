/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.LocalCount
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.TameTac
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.TameV

/-!
# Tier of the local simulation

One packed step is a sum of `width k` digits times `R^i`, and every digit is
computed from digits of the old configuration (which are below `R`), so the
step's tier does not depend on the old configuration's tier (`tm_stepT`).
Hence the replay fold keeps a fixed tier (`tm_runT`).
-/

public section

namespace Cslib.Complexity.NtimeDspace.ProgTerm

open Term LocalSim _root_.Turing

variable {w : List Bool} {L : ℕ} {env : List ℕ} {k s : ℕ} {State : Type} [DecidableEq State]
  {e : State ≃ Fin s} {machine : MultiTapePTM k Bool State}

/-- A table lookup has tier `1` when its values and its size are below `2^L`. -/
theorem tm_tabT (f : ℕ → ℕ) (N : ℕ) {dx : ℕ} (hL : 8 ≤ L) (hN : N < 2 ^ L)
    (hf : ∀ i < N, f i < 2 ^ L) : TmF w L (tabT f N) dx 1 env := by
  intro env' he x hx
  induction N with
  | zero => exact t_const (lit_lt_two_pow (by omega) (by omega))
  | succ N ih =>
    have ih' := ih (by omega) (fun i hi => hf i (by omega))
    have hc : Tm w L 1 (const N) env' := t_const (by omega)
    have hfN : Tm w L 1 (const (f N)) env' := t_const (hf N (by omega))
    simp only [tabT]
    refine (t_ite (d1 := 1) ?_ hfN ih').mono (by omega)
    unfold eqT
    exact (tm_sub (t_const (lit_lt_two_pow (by omega) (by omega)))
      (tm_add (t_lt hx hc (by omega)) (t_lt hc hx (by omega)) le_rfl le_rfl (by omega) (by omega)))

theorem tm_stepT {R N : Term} (hL : 8 ≤ L) (hR : Tm w L 1 R env) (hRpos : Pos w L R env)
    (hN : Tm w L 1 N env) (hconst : 4 * k + s + 100 < 2 ^ L)
    (hwk : width k < 2 ^ L) (hkc : keyCount k s < 2 ^ L) (hkck : keyCount k s * k < 2 ^ L)
    (hW : Le w L (const (width k)) (width k) env)
    (hpowR : TmFv w L (fun i => powT R i) 4 (width k) 1 env)
    (hK : Le w L (const k) k env) (hpow3 : TmFv w L (fun h => powT (const 3) h) 4 k 1 env)
    (hfSt : TmF w L (tabT (fSt e machine) (keyCount k s)) 16 1 env)
    (hfIn : TmF w L (tabT (fIn e machine) (keyCount k s)) 16 1 env)
    (hfOut : TmF w L (tabT (fOut e machine) (keyCount k s)) 16 1 env)
    (hfEmit : TmF w L (tabT fEmit 9) 16 1 env)
    (hfW : TmF w L (tabT (fW e machine) (keyCount k s * k)) 16 1 env)
    (hfM : TmF w L (tabT (fM e machine) (keyCount k s * k)) 16 1 env) :
    TmF2 w L (fun a b => stepT e machine R N a b) 32 1 16 env := by
  tame

/-- The replay of `b` coins keeps tier `16`. -/
theorem tm_runT {R N bT : Term} (hL : 8 ≤ L) (hR : Tm w L 1 R env) (hRpos : Pos w L R env)
    (hN : Tm w L 1 N env) (hb : Tm w L 1 bT env) (hconst : 4 * k + s + 100 < 2 ^ L)
    (hwk : width k < 2 ^ L) (hkc : keyCount k s < 2 ^ L) (hkck : keyCount k s * k < 2 ^ L)
    (hW : Le w L (const (width k)) (width k) env)
    (hpowR : TmFv w L (fun i => powT R i) 4 (width k) 1 env)
    (hK : Le w L (const k) k env) (hpow3 : TmFv w L (fun h => powT (const 3) h) 4 k 1 env)
    (hfSt : TmF w L (tabT (fSt e machine) (keyCount k s)) 16 1 env)
    (hfIn : TmF w L (tabT (fIn e machine) (keyCount k s)) 16 1 env)
    (hfOut : TmF w L (tabT (fOut e machine) (keyCount k s)) 16 1 env)
    (hfEmit : TmF w L (tabT fEmit 9) 16 1 env)
    (hfW : TmF w L (tabT (fW e machine) (keyCount k s * k)) 16 1 env)
    (hfM : TmF w L (tabT (fM e machine) (keyCount k s * k)) 16 1 env) :
    TmF2 w L (fun x st => runT e machine R N bT x st) 4 32 32 env := by
  have hstep := tm_stepT (e := e) (machine := machine) hL hR hRpos hN hconst hwk hkc hkck hW hpowR
      hK
    hpow3 hfSt hfIn hfOut hfEmit hfW hfM
  intro env' he x st hx hst
  unfold runT
  refine tm_foldT (hb.ext he) (by omega) hst (fun env'' he' acc j hacc hj => ?_) (by omega)
  exact (hstep.app (he'.trans he) hacc (t_bit (hx.ext he') hj (by omega))).mono (by omega)

end Cslib.Complexity.NtimeDspace.ProgTerm
