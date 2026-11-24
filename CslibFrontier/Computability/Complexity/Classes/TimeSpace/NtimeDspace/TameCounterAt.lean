/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.DeciderValues
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.NetSystemSpec
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.TameIte
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.TameV
public import Mathlib.NumberTheory.Chebyshev

/-!
# Tier of stable powers

`tm_powT_stable`: a power of stable terms has tier `1` when its value is below `2^L`.
-/

public section

namespace Cslib.Complexity.NtimeDspace.ProgTerm

open Term Cslib.Complexity.CountingSimulation LocalSim

variable {k s c : ℕ} {State : Type} [DecidableEq State] {machine : Turing.MultiTapePTM k Bool State}
  {e : State ≃ Fin s} {w : List Bool} {L : ℕ}

/-- Stable powers have tier `1` when their values are below `2^L`. -/
theorem tm_powT_stable {x y : Term} {env : List ℕ} {dx dy : ℕ} (hL : 8 ≤ L)
    (hx : Tm w L dx x env) (hxs : StableAt w x env) (hy : Tm w L dy y env) (hys : StableAt w y env)
    (hdy : dy ≤ 32) (hdx : dx ≤ 100)
    (hv : x.denote w env ^ y.denote w env < 2 ^ L) : Tm w L 1 (powT x y) env :=
  t_powT hx hxs hy hdy le_rfl (by omega) (fun pre _ => by rw [hxs pre, hys pre, one_mul]; exact hv)
    (by omega) (by omega)

end Cslib.Complexity.NtimeDspace.ProgTerm
