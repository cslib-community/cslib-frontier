/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.LocalStart
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.TameNetParts
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.TameV

/-!
# Tier of the local simulation's start configuration

The packing sums `leftT`/`rightT` use `3^j` for `j` below the window length
`3b` (offsets are below `b`), and the start term packs `width k` digits with
`R^i`. Each step is a small `tame1` run with the needed bounds in context.
-/

public section

namespace Cslib.Complexity.NtimeDspace.ProgTerm

open Term LocalSim _root_.Turing

variable {w : List Bool} {L : ℕ} {env : List ℕ} {k s : ℕ}

theorem TmFv.ext {f : Term → Term} {da V d : ℕ} (h : TmFv w L f da V d env) {env' : List ℕ}
    (he : Ext L env' env) : TmFv w L f da V d env' :=
  fun e2 h2 x hx hxs hxv => h e2 (h2.trans he) x hx hxs hxv

theorem tm_leftT {cellI : Term → Term} {baseT posT : Term} {V : ℕ} (hL : 8 ≤ L)
    (hcell : TmF w L cellI 12 1 env) (hbase : Tm w L 8 baseT env) (hpos : Tm w L 8 posT env)
    (hposV : Le w L posT V env) (h3 : TmFv w L (fun j => powT (const 3) j) 8 V 1 env) :
    Tm w L 12 (leftT cellI baseT posT) env := by
  unfold leftT
  tame1

theorem tm_rightT {cellI : Term → Term} {baseT posT LT : Term} {V : ℕ} (hL : 8 ≤ L)
    (hcell : TmF w L cellI 12 1 env) (hbase : Tm w L 8 baseT env) (hpos : Tm w L 8 posT env)
    (hLT : Tm w L 4 LT env)
    (hLV : Le w L LT V env) (h3 : TmFv w L (fun j => powT (const 3) j) 8 V 1 env) :
    Tm w L 12 (rightT cellI baseT posT LT) env := by
  unfold rightT
  tame1

theorem tm_startCompT {bT NT JpT JmT stI trI : Term} {offI cellI : Term → Term} {b : ℕ}
    (hL : 8 ≤ L) (hb : Tm w L 1 bT env) (hbs : StableAt w bT env) (hbv : bT.denote w env = b)
    (hN : Tm w L 1 NT env) (hJp : Tm w L 8 JpT env) (hJm : Tm w L 8 JmT env)
    (hstI : Tm w L 8 stI env) (htrI : Tm w L 8 trI env)
    (hoff : TmF w L offI 8 1 env)
    (hoffV : ∀ env', Ext L env' env → ∀ x, (offI x).denote w env' < b)
    (hcell : TmF w L cellI 12 1 env)
    (h3 : TmFv w L (fun j => powT (const 3) j) 8 (3 * b) 1 env)
    (h3b : Le w L (mul (const 3) bT) (3 * b) env) :
    TmF w L (startCompT bT NT JpT JmT stI trI offI cellI) 4 16 env := by
  intro env' he i hi
  have hbe := hb.ext he
  have hie : Tm w L 8 (add (div (sub i (const 3)) (const 4)) (const 1)) env' := by tame1
  have hbase : Tm w L 8 (mul (div (sub i (const 3)) (const 4)) (mul (const 3) bT)) env' := by tame1
  have hpos : Tm w L 8 (add bT (offI (add (div (sub i (const 3)) (const 4)) (const 1)))) env' := by
    have := hoff.app he (hie)
    tame1
  have hposV : Le w L (add bT (offI (add (div (sub i (const 3)) (const 4)) (const 1))))
      (3 * b) env' := by
    intro pre hp
    have h1 := hoffV _ (Ext.trans ⟨pre, hp, rfl⟩ he)
        (add (div (sub i (const 3)) (const 4)) (const 1))
    rw [denote_add, hbs.extend'_eq (Ext.trans ⟨pre, hp, rfl⟩ he), hbv]
    omega
  have hLT : Tm w L 4 (mul (const 3) bT) env' := by tame1
  have hleft := tm_leftT hL (hcell.ext he) hbase hpos hposV (h3.ext he)
  have hright := tm_rightT hL (hcell.ext he) hbase hpos hLT (h3b.ext he) (h3.ext he)
  unfold startCompT
  tame1

theorem tm_startT {R bT NT JpT JmT stI trI : Term} {offI cellI : Term → Term} (hL : 8 ≤ L)
    (hwk : width k < 2 ^ L) (hW : Le w L (const (width k)) (width k) env)
    (hpowR : TmFv w L (fun i => powT R i) 4 (width k) 1 env)
    (hsc : TmF w L (startCompT bT NT JpT JmT stI trI offI cellI) 4 16 env) :
    Tm w L 20 (startT k R bT NT JpT JmT stI trI offI cellI) env := by
  unfold startT
  tame1

end Cslib.Complexity.NtimeDspace.ProgTerm
