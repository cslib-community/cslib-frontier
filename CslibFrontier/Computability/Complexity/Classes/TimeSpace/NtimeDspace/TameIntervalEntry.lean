/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.NetIntervalEntry
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.TameInterval
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.TameStart

/-!
# Tier of an interval entry

The interval entry runs the interval count on the window data decoded from
the letters `L`; each piece is a small `tame1` run.
-/

public section

namespace Cslib.Complexity.NtimeDspace.ProgTerm

open Term LocalSim _root_.Turing

variable {w : List Bool} {L : ℕ} {env : List ℕ} {k s : ℕ} {State : Type} [DecidableEq State]
  {e : State ≃ Fin s} {machine : MultiTapePTM k Bool State}

set_option maxHeartbeats 1000000 in
-- `tame1` tier-rule search over the unfolded program term, with `omega` side goals; measured
-- ~320912 heartbeats
omit [DecidableEq State] in
theorem tm_intervalEntryT {RT NT qT bT σT iT : Term} {Lf : Term → Term} {b : ℕ} (hL : 8 ≤ L)
    (hR : Tm w L 1 RT env) (hRpos : Pos w L RT env) (hN : Tm w L 1 NT env) (hq : Tm w L 1 qT env)
    (hb : Tm w L 1 bT env) (hbs : StableAt w bT env) (hbv : bT.denote w env = b) (hbpos : 0 < b)
    (hbp : Pos w L bT env) (hσ : Tm w L 1 σT env)
    (hconst : 4 * k + s + 100 < 2 ^ L) (hinit : LocalSim.stc e (some machine.initial) < 2 ^ L)
    (hwk : width k < 2 ^ L) (hW : Le w L (const (width k)) (width k) env)
    (hpowR : TmFv w L (fun i => powT RT i) 4 (width k) 1 env)
    (h3 : TmFv w L (fun j => powT (const 3) j) 8 (3 * b) 1 env)
    (h3b : Le w L (mul (const 3) bT) (3 * b) env)
    (hcr : Tm w L 1 (powT bT (const (k + 1))) env) (hcc : Tm w L 1 (ccountT k s bT) env)
    (h2b : Tm w L 1 (pow2 bT) env)
    (hrun : TmF2 w L (fun x st => runT e machine RT NT bT x st) 4 32 32 env)
    (hLf : TmF w L Lf 16 8 env) (hi : Tm w L 4 iT env) :
    Tm w L 32 (intervalEntryT e machine RT NT qT bT σT Lf iT) env := by
  have hJp : Tm w L 8 (digitCountT k σT (const 0) (const 2) iT) env := by unfold digitCountT; tame1
  have hJm : Tm w L 8 (digitCountT k σT (const 0) (const 0) iT) env := by unfold digitCountT; tame1
  have hstI : Tm w L 8 (inStT k s (LocalSim.stc e (some machine.initial)) bT Lf iT) env := by
    unfold inStT; tame1
  have htrI : Tm w L 8 (inTrT k s bT Lf iT) env := by unfold inTrT; tame1
  have hstO : Tm w L 8 (ctlStT k s bT (Lf iT)) env := by tame1
  have htrO : Tm w L 8 (ctlTrT k bT (Lf iT)) env := by tame1
  have hoffO : TmF w L (fun c => ctlOffT k bT (Lf iT) c) 8 8 env := by tame1
  have hdC : TmF w L (fun c => sdigT k σT c iT) 8 8 env := by tame1
  have hcellO : TmF w L (outCellT k s qT bT Lf iT) 8 8 env := by tame1
  have hoff : TmF w L (inOffT k s bT Lf iT) 8 1 env := by tame1
  have hcell : TmF w L (inCellT k s qT bT σT Lf iT) 12 1 env := by tame1
  have hoffV : ∀ env', Ext L env' env → ∀ x, (inOffT k s bT Lf iT x).denote w env' < b := by
    intro env' he x
    have := inOffT_lt (k := k) (s := s) (Lf := Lf) (iT := iT) x
        (by rw [hbs.extend'_eq he, hbv]; exact hbpos)
    rwa [hbs.extend'_eq he, hbv] at this
  have hsc := tm_startCompT (NT := NT) hL hb hbs hbv hN hJp hJm hstI htrI hoff hoffV hcell h3 h3b
  have hstart := tm_startT (k := k) hL hwk hW hpowR hsc
  have hcount := tm_intervalCountT (e := e) (machine := machine) hL hR hRpos hb hconst
      hJp hJm hstO htrO
    hoffO hdC hcellO h2b hrun hstart
  unfold intervalEntryT
  exact (t_ite (by unfold guardT; tame1) hcount
      (t_const (lit_lt_two_pow (by omega) (by omega)))).mono
    (by omega)

end Cslib.Complexity.NtimeDspace.ProgTerm
