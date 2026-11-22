/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.NetPortTerm
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.TameNetParts
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.TameV

/-!
# Tiers of the network's graph terms

Window searches, edge targets and sources, port predicates, counts and
positions, each as a function of its varying arguments.
-/

public section

namespace Cslib.Complexity.NtimeDspace.ProgTerm

open Term LocalSim _root_.Turing

variable {w : List Bool} {L : ℕ} {env : List ℕ} {k : ℕ}

section Graph

variable {qT mT σT : Term} (hL : 8 ≤ L) (hq : Tm w L 1 qT env) (hm : Tm w L 1 mT env)
  (hσ : Tm w L 1 σT env) (hconst : 4 * k + 100 < 2 ^ L)
include hL hq hm hσ hconst

omit hm in
theorem tm_edgeTargetT : TmF w L (edgeTargetT k qT σT) 16 20 env := by
  intro env' he n hn
  unfold edgeTargetT
  tame1

theorem tm_explicitSrcT : TmF w L (explicitSrcT k qT mT σT) 16 24 env := by
  have het := tm_edgeTargetT (k := k) hL hq hσ hconst
  intro env' he n hn
  unfold explicitSrcT
  tame1

omit hσ in
theorem tm_explicitTgtT : TmF w L (explicitTgtT k qT mT) 16 24 env := by
  intro env' he n hn
  unfold explicitTgtT
  tame1

theorem tm_portPredT : TmF2 w L (portPredT k qT mT σT) 16 16 1 env := by
  have hs := tm_explicitSrcT (k := k) hL hq hm hσ hconst
  have ht := tm_explicitTgtT (k := k) hL hq hm hconst
  intro env' he v x hv hx
  unfold portPredT
  tame1

theorem tm_portCountT : TmF2 w L (portCountT k qT mT σT) 16 16 20 env := by
  have hp := tm_portPredT (k := k) hL hq hm hσ hconst
  intro env' he v lim hv hlim
  unfold portCountT
  tame1

theorem tm_portIdxT : TmF2 w L (portIdxT k qT mT σT) 16 16 20 env := by
  have hp := tm_portPredT (k := k) hL hq hm hσ hconst
  have hc := tm_portCountT (k := k) hL hq hm hσ hconst
  intro env' he v x hv hx
  unfold portIdxT
  tame1

end Graph

end Cslib.Complexity.NtimeDspace.ProgTerm
