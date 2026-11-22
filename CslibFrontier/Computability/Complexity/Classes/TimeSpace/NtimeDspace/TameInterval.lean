/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.NetIntervalTerm
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.TameNetParts
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.TameV

/-!
# Tier of the interval count

`intervalCountT` sums a 0/1 acceptance test over `2^b` coin strings of the
replay from the start configuration; its tier follows from the replay and
start tiers, with the window functions as hypotheses.
-/

public section

namespace Cslib.Complexity.NtimeDspace.ProgTerm

open Term LocalSim _root_.Turing

variable {w : List Bool} {L : ℕ} {env : List ℕ} {k s : ℕ} {State : Type} [DecidableEq State]
  {e : State ≃ Fin s} {machine : MultiTapePTM k Bool State}

theorem tm_intervalCountT {R NT bT JpT JmT stI trI stO trO : Term}
    {offI cellI offO dC cellO : Term → Term} (hL : 8 ≤ L)
    (hR : Tm w L 1 R env) (hRpos : Pos w L R env) (hb : Tm w L 1 bT env)
    (hconst : 4 * k + s + 100 < 2 ^ L)
    (hJp : Tm w L 8 JpT env) (hJm : Tm w L 8 JmT env) (hstO : Tm w L 8 stO env)
        (htrO : Tm w L 8 trO env)
    (hoffO : TmF w L offO 8 8 env) (hdC : TmF w L dC 8 8 env) (hcellO : TmF w L cellO 8 8 env)
    (h2b : Tm w L 1 (pow2 bT) env)
    (hrun : TmF2 w L (fun x st => runT e machine R NT bT x st) 4 32 32 env)
    (hstart : Tm w L 20 (startT k R bT NT JpT JmT stI trI offI cellI) env) :
    Tm w L 32 (intervalCountT e machine R NT bT JpT JmT stI trI stO trO offI cellI offO dC cellO)
        env := by
  unfold intervalCountT
  tame1

theorem inOffT_lt {bT : Term} {Lf : Term → Term} {iT : Term} {env : List ℕ} (x : Term)
    (hbpos : 0 < bT.denote w env) : (inOffT k s bT Lf iT x).denote w env < bT.denote w env := by
  unfold inOffT
  simp only [denote_ite]
  split_ifs
  · simp only [denote_const]; exact hbpos
  · unfold ctlOffT; rw [denote_mod]; exact Nat.mod_lt _ hbpos
  · simp only [denote_const]; exact hbpos

end Cslib.Complexity.NtimeDspace.ProgTerm
