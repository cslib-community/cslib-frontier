/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.NetValueBound
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.TameGraph
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.TameIntervalEntry
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.TameIte

/-!
# Tier of the network's table entries

The letters of a vertex (a sum of bits times `2^r` for `r` below the letter
width), the entries of the old network, the table entry, and the weight.
-/

public section

namespace Cslib.Complexity.NtimeDspace.ProgTerm

open Term LocalSim _root_.Turing

variable {w : List Bool} {L : ℕ} {env : List ℕ} {k s : ℕ} {State : Type} [DecidableEq State]
  {e : State ≃ Fin s} {machine : MultiTapePTM k Bool State}

set_option maxHeartbeats 2000000 in
-- `tame1` tier-rule search over the unfolded program term, with `omega` side goals; measured
-- ~832525 heartbeats
theorem tm_lettersT {qT bT σT vT jT : Term} {m0 : ℕ} (hL : 8 ≤ L)
    (hq : Tm w L 1 qT env) (hb : Tm w L 1 bT env) (hσ : Tm w L 1 σT env)
    (hv : Tm w L 4 vT env) (hj : Tm w L 4 jT env) (hconst : 4 * k + s + 100 < 2 ^ L)
    (hlet : TmFv w L (fun r => powT (const 2) r) 4 m0 1 env)
    (hletLe : Le w L (letterBitsT k s bT) m0 env) :
    TmF w L (lettersT k qT (letterBitsT k s bT) σT vT jT) 16 8 env := by
  unfold lettersT
  tame1

theorem TmF2v.retier' {f : Term → Term → Term} {da V db d d' : ℕ} (h : TmF2v w L f da V db d env)
    (hv : ∀ env', Ext L env' env → ∀ x y, (f x y).denote w env' < 2 ^ (d' * L)) :
    TmF2v w L f da V db d' env :=
  fun env' he x y hx hxs hxv hy hys pre hp =>
    ⟨(h env' he x y hx hxs hxv hy hys pre hp).1, hv _ (Ext.trans ⟨pre, hp, rfl⟩ he) x y⟩

section Entry

variable {RT NT qT bT σT : Term} {b m0 : ℕ} (hL : 8 ≤ L)
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
    (hlet : TmFv w L (fun r => powT (const 2) r) 4 m0 1 env)
    (hletLe : Le w L (letterBitsT k s bT) m0 env) (hm0 : m0 < 2 ^ L)
include hL hR hRpos hN hq hb hbs hbv hbpos hbp hσ hconst hinit hwk hW hpowR h3 h3b hcr hcc h2b hrun
  hlet hletLe hm0

omit [DecidableEq State] hL hR hRpos hN hq hbv hbpos hbp hσ hinit hwk hW hpowR h3 h3b hcr hcc
    h2b hrun hlet in
theorem tm_letterBitsT : Tm w L 1 (letterBitsT k s bT) env := by
  refine tm_retier (d := 4) (by unfold letterBitsT; tame1) ((stableAt_const _ _).mul hbs) ?_
  have := hletLe [] Small.nil
  simp only [List.nil_append] at this
  rw [one_mul]; omega

omit [DecidableEq State] in
theorem tm_tableEntryT {vT jT : Term} (hv : Tm w L 4 vT env) (hj : Tm w L 4 jT env) :
    Tm w L 32 (tableEntryT k s e machine RT NT qT bT σT vT jT) env := by
  have hm1 := tm_letterBitsT hb hbs hconst hletLe hm0
  have hc' : 4 * k + 100 < 2 ^ L := by omega
  have hbSm : Sm w L bT (3 * b) env := Sm.of_stable hbs (by rw [hbv]; omega)
  have het := tm_edgeTargetT (k := k) hL hq hσ hc'
  have hpp := tm_portPredT (k := k) hL hq hm1 hσ hc'
  have hpi := tm_portIdxT (k := k) hL hq hm1 hσ hc'
  have hLf := tm_lettersT (vT := vT) (jT := jT) hL hq hb hσ hv hj hconst hlet hletLe
  have hint := tm_intervalEntryT (e := e) (machine := machine) (qT := qT) (σT := σT) hL
      hR hRpos hN hq hb
    hbs hbv hbpos hbp hσ hconst hinit hwk hW hpowR h3 h3b hcr hcc h2b hrun hLf hv
  have hold : Tm w L 32 (oldEntryT k s e machine RT NT qT bT σT
      (lettersT k qT (letterBitsT k s bT) σT vT jT) vT) env := by
    unfold oldEntryT
    refine (t_ite (by tame1) hint (t_ite (by tame1) (by unfold acceptT; tame1)
      (t_const (lit_lt_two_pow (by omega) (by omega))))).mono (by omega)
  unfold tableEntryT
  refine (t_ite (by tame1) (t_ite (by unfold LocalSim.validT; tame1) hold
    (t_const (lit_lt_two_pow (by omega) (by omega)))) (by tame1)).mono (by omega)

omit [DecidableEq State] in
theorem tm_weightNT {mv : ℕ} (hpa : TmFv w L
    (fun e' => pow2 (arityNT k s qT bT σT e')) 4 mv 1 env) :
    TmF2v w L (weightNT k s e machine RT NT qT bT σT) 4 mv 4 32 env := by
  intro env' he v A hv hvs hvv hA hAs
  have hj : Tm w L 4 (mod A (pow2 (arityNT k s qT bT σT v))) env' :=
    t_mod_left hA (hpa.app he hv hvs hvv)
  unfold weightNT
  exact tm_tableEntryT (env := env') hL (hR.ext he) (hRpos.ext he) (hN.ext he)
      (hq.ext he) (hb.ext he)
    (hbs.extend' he) (by rw [hbs.extend'_eq he, hbv]) hbpos (hbp.ext he) (hσ.ext he)
        hconst hinit hwk
    (hW.ext he) (hpowR.ext he) (h3.ext he) (h3b.ext he) (hcr.ext he) (hcc.ext he) (h2b.ext he)
    (hrun.ext he) (hlet.ext he) (hletLe.ext he) hm0 hv hj

omit [DecidableEq State] in
/-- The weight has tier `1` when `2^b < 2^L`. -/
theorem tm_weightNT1 {mv : ℕ} (hpa : TmFv w L (fun e' => pow2 (arityNT k s qT bT σT e')) 4 mv 1 env)
    (h2bv : 2 ^ b < 2 ^ L) : TmF2v w L (weightNT k s e machine RT NT qT bT σT) 4 mv 4 1 env := by
  classical
  refine TmF2v.retier' (tm_weightNT hL hR hRpos hN hq hb hbs hbv hbpos hbp hσ hconst
      hinit hwk hW hpowR
    h3 h3b hcr hcc h2b hrun hlet hletLe hm0 hpa) (fun env' he x y => ?_)
  have := weightNT_le (w := w) (k := k) (s := s) (e := e) (machine := machine) RT NT
      qT bT σT x y env'
  rw [hbs.extend'_eq he, hbv] at this
  rw [one_mul]; omega

end Entry

end Cslib.Complexity.NtimeDspace.ProgTerm
