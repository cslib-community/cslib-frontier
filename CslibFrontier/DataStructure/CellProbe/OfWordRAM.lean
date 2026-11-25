/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.CellProbe.OfWordRAM
public import CslibFrontier.DataStructure.CellProbe.Randomized.ObliviousSequence
public import CslibFrontier.DataStructure.WordRAM.Randomized.ObliviousSequence
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.SupportTsum

/-!
# Word-RAM-to-Cell-Probe Data-Structure Simulation Bridges and Lower-Bound Transfer

This file lifts the program-level Word-RAM-to-cell-probe simulators of
`CslibFrontier.Computability.CellProbe.OfWordRAM` (deterministic cell-probe model and
constant-register RAM lower-bound note in [Miltersen1999], §1.2, pp. 1–2; multi-register spilling,
wide-cell packing, `zeroOutside` framing, and Las Vegas truncation are local library constructions)
to the relational and oblivious-sequence data-structure `Impl` hierarchies
(`Cslib.DataStructure.WordRAM` → `Cslib.DataStructure.CellProbe`, [CLRS2009], Section 17.3).
Combining these bridges with the zero-error averaging direction of Yao's principle [Yao1977]
transfers deterministic step-indexed `IndexedScheme` lower bounds against zero-error
implementations on oblivious sequences: the `StateTransitionImpl` and `ObliviousSequenceImpl`
transfers lower-bound the certified potential-amortized resource budget
(`initPotential + E[totalCost charge + overhead · length]` and
`initPotential + E[(ops.map charge).sum + overhead · length]`), while the flat `(ν₀, p_op)`
transfers directly lower-bound expected `ExecFlatProgramOps` instructions
(`E[timeBound ops + overhead · length]`). Bounded-error (Monte Carlo) and adaptive-adversary
cell-probe lower-bound transfers remain separate directions.

Four simulation and transfer layers are provided across the **standard `w`-bit layout**
(`space + persistentRegCount P` cells of width `w`, additive overhead `2 * persistentRegCount P`,
which equals `0` extra cells and `0` extra probes when `∀ i, P.input i = true`) and, for the main
implementation and lower-bound transfer theorems, the **wide-cell single-spill layout** (`space + 1`
cells of width `wideSubroutineWidth P w`, additive overhead at most `2` regardless of register count
`r`):
1. **Deterministic `WordRAM.StateTransitionImpl` (`toCellProbe`, `toCellProbeWide`, `simInit`):**
   Uses `rep_supported` and `potential_supported` with `zeroOutside` so no extra read-footprint
   hypothesis is required on `WordRAM.StateTransitionImpl`; pre-operation initialization is packed
   into `Scheme.init` at `0` operation probes, and `simInit` (in standard `w`-bit layout)
   additionally simulates `P.initFresh` from zeroed cell memory in at most
   `C.initTime + persistentRegCount P` probes.
2. **Flat `(ν₀, p_op)` pairs (`ExecFlatProgramOps`, `exists_cellProbe_of_flatPrograms`,
   `exists_cellProbeWide_of_flatPrograms`, `flat_wordRAM_lower_bound_of_det_cellProbe`,
   `flat_wordRAM_lower_bound_of_det_cellProbe_wide`):** Direct multi-operation Las Vegas bridge
   coupling an initial state distribution `ν₀` with a flat `p_op : WordRAM.Program B r` without
   wrapping `SubroutineCode`.
3. **Randomized Las Vegas `WordRAM.Randomized.StateTransitionImpl` (`exists_cellProbe_lasVegas`,
   `exists_cellProbeWide_lasVegas`, `wordRAM_lower_bound_of_det_cellProbe_lower_bound`,
   `wordRAM_lower_bound_of_det_cellProbe_wide`):** Buffered finite-horizon truncation preserves
   **100% zero-error transcript correctness** on all admissible histories over `opsAlphabet` up to
   `M_corr` (without `[Fintype D.Op]`), and taking `η → 0` eliminates truncation slack completely
   from the contrapositive Word-RAM lower bound.
4. **Randomized `WordRAM.Randomized.ObliviousSequenceImpl` (`exists_cellProbe_of_execRand`,
   `exists_cellProbe_lasVegas`, `oblivious_wordRAM_lower_bound_of_det_cellProbe`,
   `oblivious_wordRAM_lower_bound_of_det_cellProbe_wide`):** Exact zero-slack standard-layout
   simulation for finite-tree `ExecRand` on arbitrary `ObliviousSequenceSpec`s (including Monte
   Carlo contracts), standard-layout buffered zero-error simulation, and both standard- and
   wide-layout contrapositive lower-bound transfers on `D.toObliviousSequenceSpec s₀`.

## Main definitions

* `Cslib.DataStructure.WordRAM.StateTransitionImpl.toCellProbe`,
  `Cslib.DataStructure.WordRAM.StateTransitionImpl.toCellProbeWide`,
  `Cslib.DataStructure.WordRAM.StateTransitionImpl.simInit`: deterministic `StateTransitionImpl`
  simulation bridges and fresh-initializer probe tree.
* `Cslib.DataStructure.CellProbe.prepareFlatRegs`,
  `Cslib.DataStructure.CellProbe.ExecFlatProgramOps`,
  `Cslib.DataStructure.CellProbe.flatStateDist`,
  `Cslib.DataStructure.CellProbe.flatExpectedBodyTime`,
  `Cslib.DataStructure.CellProbe.flatExpectedTime`: flat `(ν₀, p_op)` multi-operation Las Vegas
  execution contract, plus boundary state distribution and intrinsic expected running times on
  certified `ExecFlatProgramOps` histories.
* `Cslib.DataStructure.WordRAM.Randomized.ExecStepsRand`,
  `Cslib.DataStructure.WordRAM.Randomized.ObliviousSequenceImpl.HasFiniteExecRand`: finite-tree
  `ExecRand` step witness for exact zero-slack oblivious-sequence simulation.

## Main results

* `Cslib.DataStructure.CellProbe.ExecFlatProgramOps.tighten_actualBodyTime`,
  `Cslib.DataStructure.CellProbe.flatExpectedTime_eq_add_length`: checked actual-time tightening
  bridge showing every certified `ExecFlatProgramOps` admits the exact intrinsic expected non-`halt`
  body instruction count `flatExpectedBodyTime` (`≤ T_ops`), preserving coupled distributions and
  correctness.
* `Cslib.DataStructure.CellProbe.exists_cellProbe_of_flatPrograms`,
  `Cslib.DataStructure.CellProbe.exists_cellProbeWide_of_flatPrograms`,
  `Cslib.DataStructure.CellProbe.flat_wordRAM_lower_bound_of_det_cellProbe`,
  `Cslib.DataStructure.CellProbe.flat_wordRAM_lower_bound_of_det_cellProbe_wide`: flat-program
  simulation and contrapositive lower-bound transfer.
* `Cslib.DataStructure.WordRAM.Randomized.StateTransitionImpl.exists_cellProbe_lasVegas`,
  `Cslib.DataStructure.WordRAM.Randomized.StateTransitionImpl.exists_cellProbeWide_lasVegas`,
  `Cslib.DataStructure.CellProbe.wordRAM_lower_bound_of_det_cellProbe_lower_bound`,
  `Cslib.DataStructure.CellProbe.wordRAM_lower_bound_of_det_cellProbe_wide`: Las Vegas
  `StateTransitionImpl` simulation and `η`-free contrapositive Word-RAM lower-bound transfer over an
  explicit `opsAlphabet : Finset D.Op` (plus `_of_fintype` corollaries).
* `Cslib.DataStructure.WordRAM.Randomized.ObliviousSequenceImpl.exists_cellProbe_of_execRand`,
  `Cslib.DataStructure.WordRAM.Randomized.ObliviousSequenceImpl.exists_cellProbe_lasVegas`,
  `Cslib.DataStructure.CellProbe.oblivious_wordRAM_lower_bound_of_det_cellProbe`,
  `Cslib.DataStructure.CellProbe.oblivious_wordRAM_lower_bound_of_det_cellProbe_wide`:
  `ObliviousSequenceImpl` simulation and contrapositive lower-bound transfer.

## References

* [P. B. Miltersen, *Cell Probe Complexity — a Survey*, §1.2][Miltersen1999]
* [A. C.-C. Yao, *Probabilistic Computations: Toward a Unified Measure of Complexity*][Yao1977]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Section 17.3][CLRS2009]
-/

public section

open Cslib.WordRAM Cslib.CellProbe Cslib.Probability
open scoped ENNReal

namespace Cslib.DataStructure.CellProbe

/-! ### 0. Shared `ENNReal`, worst-case horizon, and initial-state helpers -/

/-- Eliminate arbitrary per-step truncation slack `η > 0` in `ℝ≥0∞`: if `LB ≤ R + η * M` holds for
every `0 < η`, then `LB ≤ R`. -/
theorem le_of_forall_pos_le_add_mul {LB R : ℝ≥0∞} {M : ℕ}
    (h : ∀ {η : ℝ≥0∞}, 0 < η → LB ≤ R + η * (M : ℝ≥0∞)) : LB ≤ R :=
  ENNReal.le_of_forall_pos_le_add fun ε hε _ =>
    (h (ENNReal.div_pos (ENNReal.coe_pos.mpr hε).ne' (ENNReal.natCast_ne_top M))).trans
      (add_le_add le_rfl (by rw [mul_comm]; exact ENNReal.mul_div_le))

/-- If every single-operation tree of `Q` has expected probes at most `W` on every memory, then
`Q.expectedProbesFrom m ops ≤ ops.length * W` on every memory `m`. -/
theorem expectedProbesFrom_le_mul {Op : Type*} {Result : Op → Type} {cells w : ℕ}
    (Q : Cslib.CellProbe.Randomized.Scheme Op Result cells w) (W : ℝ≥0∞)
    (hW : ∀ o m, (Q.step o).expectedProbes m ≤ W) :
    ∀ (ops : List Op) (m : Mem cells w),
      Q.expectedProbesFrom m ops ≤ (ops.length : ℝ≥0∞) * W
  | [], _ => by simp [Cslib.CellProbe.Randomized.Scheme.expectedProbesFrom]
  | o :: ops, m => by
    rw [Q.expectedProbesFrom_cons]
    exact (add_le_add (hW o m)
      (Probability.PMF.tsum_mul_le_of_forall_le (((Q.step o).run m).map Prod.fst)
        fun am => expectedProbesFrom_le_mul Q W hW ops am.2)).trans_eq
      (by simp only [List.length_cons, Nat.cast_add, Nat.cast_one]; ring)

/-- Construct a canonical zeroed-memory initial `Data r_ds` for a zero-parameter
`SubroutineCode B r_ds 0` from `Fits w base` alone. -/
def mkInitData0 {B : Basis} {r_ds : ℕ} (P : SubroutineCode B r_ds 0) (base : ℕ) : Data r_ds where
  regs i := if i = P.frontierReg then base else 0
  mem _ := 0

theorem mkInitData0_spec {B : Basis} {r_ds w base : ℕ} (P : SubroutineCode B r_ds 0)
    (params : Fin 0 → ℕ) (hfit_base : Fits w base) :
    (mkInitData0 P base).Bounded w ∧
      (mkInitData0 P base).regs P.frontierReg = base ∧
      (∀ j, (mkInitData0 P base).regs (P.initParams j) = params j) ∧
      ∀ a, (mkInitData0 P base).mem a = 0 :=
  ⟨⟨fun i => by
      dsimp only [mkInitData0]
      split_ifs
      exacts [hfit_base, fits_zero w],
    fun _ => fits_zero w⟩, by simp [mkInitData0], fun j => Fin.elim0 j, fun _ => rfl⟩

end Cslib.DataStructure.CellProbe

/-! ### 1. Deterministic `WordRAM.StateTransitionImpl` → `CellProbe.StateTransitionImpl` -/

namespace Cslib.DataStructure.WordRAM.StateTransitionImpl

open Cslib.DataStructure.CellProbe

universe u v

variable {B : Basis} {r_ds k_init w base : ℕ}
  {P : SubroutineCode B r_ds k_init}
  {D : StateTransitionSpec.{u, v, 0}} [∀ o, Inhabited (D.Result o)]
  {params : Fin k_init → ℕ} {s₀ : D.State}

omit [∀ o, Inhabited (D.Result o)] in
private theorem initFresh_zeroMem (C : WordRAM.StateTransitionImpl P D w base params s₀)
    {d₀ : Data r_ds} (hd₀ : d₀.Bounded w)
    (hfr : d₀.regs P.frontierReg = base)
    (hpar : ∀ j, d₀.regs (P.initParams j) = params j) :
    ∃ y₀, ExecWithin w P.initFresh { regs := d₀.regs, mem := fun _ => 0 } y₀ C.initTime ∧
      C.rep s₀ y₀ ∧ C.potential y₀ ≤ C.initPotential := by
  have hd₀' : ({ regs := d₀.regs, mem := fun _ => 0 } : Data r_ds).Bounded w :=
    ⟨hd₀.1, fun _ => fits_zero w⟩
  obtain ⟨y₀, he, _, hr₀, hpot₀, _⟩ :=
    C.initFresh_exec (x := { regs := d₀.regs, mem := fun _ => 0 }) hd₀' hfr hpar (fun _ _ => rfl)
  exact ⟨y₀, he, hr₀, hpot₀⟩

omit [∀ o, Inhabited (D.Result o)] in
private theorem rep_potential_unpack_pack_zero
    (C : WordRAM.StateTransitionImpl P D w base params s₀)
    {regCells wCell : ℕ} (L : RegLayout r_ds P.input base C.space w regCells wCell)
    {s : D.State} {y : Data r_ds} (hy : C.rep s y) :
    C.rep s (L.unpack (fun _ => 0) (L.pack y)) ∧
      C.potential (L.unpack (fun _ => 0) (L.pack y)) = C.potential y := by
  have hy_bdd : y.Bounded w := C.bounded hy
  have hpers : ∀ i, P.input i = false →
      (L.unpack (fun _ => 0) (L.pack y)).regs i = y.regs i := fun i hi => by
    simpa [hi] using L.unpack_pack_regs (fun _ => 0) hy_bdd i
  have hmem : ∀ a ∈ (Block.mk base C.space).footprint,
      (L.unpack (fun _ => 0) (L.pack y)).mem a = y.mem a := fun a ha => by
    rw [L.unpack_pack_mem (fun _ => 0) hy_bdd a]
    exact zeroOutside_mem_of_mem_footprint y ha
  exact ⟨C.rep_supported hpers hmem (L.unpack_bounded (fun _ _ => fits_zero w) _) hy,
    C.potential_supported hpers hmem hy⟩

/-- Unified deterministic `WordRAM.StateTransitionImpl` → `CellProbe.StateTransitionImpl` simulation
over an arbitrary `RegLayout`: uses `rep_supported` and `potential_supported` with `zeroOutside` so
no extra read-footprint hypothesis is needed on `C`. -/
noncomputable def toCellProbeLayout (C : WordRAM.StateTransitionImpl P D w base params s₀)
    {regCells wCell : ℕ} (L : RegLayout r_ds P.input base C.space w regCells wCell)
    {d₀ : Data r_ds} (hd₀ : d₀.Bounded w)
    (hfr : d₀.regs P.frontierReg = base)
    (hpar : ∀ j, d₀.regs (P.initParams j) = params j) :
    Σ P_cp : Scheme D.Op D.Result (C.space + regCells) wCell,
      { C_cp : Cslib.DataStructure.CellProbe.StateTransitionImpl D P_cp s₀ //
        C_cp.initPotential = C.initPotential ∧
          ∀ s o, C_cp.charge s o = C.charge s o + L.overhead } := by
  let hex₀ := C.initFresh_zeroMem hd₀ hfr hpar
  let y₀ := Classical.choose hex₀
  have hy₀_spec := Classical.choose_spec hex₀
  let P_cp : Scheme D.Op D.Result (C.space + regCells) wCell :=
    { init := L.pack y₀
      step := fun o =>
        simProgDetAuto L (P.code.program P.output) (C.encode o)
          (fun _ regs => C.decode o regs) default }
  refine ⟨P_cp, ⟨{
    rep := fun s m => L.ValidMem m ∧ C.rep s (L.unpack (fun _ => 0) m)
    potential := fun m => C.potential (L.unpack (fun _ => 0) m)
    initPotential := C.initPotential
    charge := fun s o => C.charge s o + L.overhead
    init_rep := ?_
    init_potential := ?_
    step_exec := ?_
  }, ⟨rfl, fun _ _ => rfl⟩⟩⟩
  · exact ⟨L.validMem_pack y₀, (C.rep_potential_unpack_pack_zero L hy₀_spec.2.1).1⟩
  · exact (C.rep_potential_unpack_pack_zero L hy₀_spec.2.1).2.le.trans hy₀_spec.2.2
  · intro s m o ⟨hm_val, hr_can⟩ hv
    let x_op := L.unpack (C.encode o) m
    have harg_fit : ∀ i, P.input i = true → Fits w (C.encode o i) := C.arguments_fit o hv
    have hx_bdd : x_op.Bounded w := L.unpack_bounded harg_fit m
    have hpers_eq : ∀ i, P.input i = false → x_op.regs i = (L.unpack (fun _ => 0) m).regs i :=
      fun i hi => L.unpack_regs_pers (C.encode o) (fun _ => 0) m i hi
    have hmem_eq : ∀ a ∈ (Block.mk base C.space).footprint,
        x_op.mem a = (L.unpack (fun _ => 0) m).mem a :=
      fun a _ => (L.unpack_mem (C.encode o) m a).trans (L.unpack_mem (fun _ => 0) m a).symm
    have hr_op : C.rep s x_op := C.rep_supported hpers_eq hmem_eq hx_bdd hr_can
    have hpot_op : C.potential x_op = C.potential (L.unpack (fun _ => 0) m) :=
      C.potential_supported hpers_eq hmem_eq hr_can
    have hregs_prep :
        x_op.regs = fun i =>
          if P.input i then C.encode o i else (L.unpack (fun _ => 0) m).regs i := by
      funext i
      by_cases hi : P.input i = true
      · simp only [hi, ↓reduceIte]
        exact L.unpack_regs_input (C.encode o) m i hi
      · have hif : P.input i = false := Bool.eq_false_iff.mpr hi
        simp [hif, hpers_eq i hif]
    have harg_match : C.argMatch o x_op.regs := by
      rw [hregs_prep]
      exact C.encode_matches o (L.unpack (fun _ => 0) m).regs
    obtain ⟨y, s', a, n, he, hdstep, hdec, hr_y, _, hamort⟩ := C.step_exec o hr_op hv harg_match
    have hhalt : step w (P.code.program P.output) ⟨0 + P.code.size, y⟩ = .halt (y.regs P.output) :=
      step_halt (by simp [Code.program])
    obtain ⟨hrun_sim, hpr_sim⟩ :=
      simProgDetAuto_spec L (P.code.program P.output) (C.encode o)
        (fun _ regs => C.decode o regs) (default : D.Result o) hm_val harg_fit
        (he.runs (pc := 0) (p := P.code.program P.output) (Program.Contains.self _).append_left)
        hhalt
    change (P_cp.step o).run m = _ at hrun_sim
    change (P_cp.step o).probes m ≤ _ at hpr_sim
    rw [hdec, Option.getD_some] at hrun_sim
    obtain ⟨hr_pack, hpot_pack⟩ := C.rep_potential_unpack_pack_zero L hr_y
    rw [hrun_sim]
    refine ⟨s', hdstep, ⟨L.validMem_pack y, hr_pack⟩, ?_⟩
    dsimp only
    rw [hpot_pack, ← hpot_op]
    omega

/-- **Bridge 1 (Deterministic `WordRAM.StateTransitionImpl.toCellProbe`):**
Any deterministic `WordRAM.StateTransitionImpl` using `C.space` words and `persistentRegCount P`
persistent registers induces a deterministic `CellProbe.StateTransitionImpl` on
`C.space + persistentRegCount P` cells of width `w` with `initPotential = C.initPotential` and
per-operation probe charge `C.charge s o + 2 * persistentRegCount P` (`0` extra cells and `0` extra
probes when `∀ i, P.input i = true`). -/
noncomputable def toCellProbe (C : WordRAM.StateTransitionImpl P D w base params s₀)
    {d₀ : Data r_ds} (hd₀ : d₀.Bounded w)
    (hfr : d₀.regs P.frontierReg = base)
    (hpar : ∀ j, d₀.regs (P.initParams j) = params j) :
    Σ P_cp : Scheme D.Op D.Result (C.space + persistentRegCount P) w,
      { C_cp : Cslib.DataStructure.CellProbe.StateTransitionImpl D P_cp s₀ //
        C_cp.initPotential = C.initPotential ∧
          ∀ s o, C_cp.charge s o = C.charge s o + 2 * persistentRegCount P } := by
  let S := C.toCellProbeLayout (standardLayout P.input base C.space w) hd₀ hfr hpar
  refine ⟨S.1, ⟨S.2.1, S.2.2.1, fun s o => (S.2.2.2 s o).trans ?_⟩⟩
  rw [standardLayout_overhead, persistentRegCount_eq_persCount]

/-- Fresh-initializer cell-probe tree for `(C.toCellProbe hd₀ hfr hpar).1`: starting from zeroed
cell memory `fun _ => 0`, simulates `P.initFresh` in at most `C.initTime + persistentRegCount P`
cell probes and leaves `(C.toCellProbe hd₀ hfr hpar).1.init` in memory. -/
noncomputable def simInit (C : WordRAM.StateTransitionImpl P D w base params s₀)
    (d₀ : Data r_ds) : ProbeTree (C.space + persistentRegCount P) w PUnit :=
  simProgInitDet (standardLayout P.input base C.space w)
    (P.initFresh.program P.output) d₀.regs (C.initTime + 1)

theorem simInit_spec (C : WordRAM.StateTransitionImpl P D w base params s₀)
    {d₀ : Data r_ds} (hd₀ : d₀.Bounded w)
    (hfr : d₀.regs P.frontierReg = base)
    (hpar : ∀ j, d₀.regs (P.initParams j) = params j) :
    (C.simInit d₀).run (fun _ => 0) = (PUnit.unit, (C.toCellProbe hd₀ hfr hpar).1.init) ∧
      (C.simInit d₀).probes (fun _ => 0) ≤ C.initTime + persistentRegCount P := by
  let hex₀ := C.initFresh_zeroMem hd₀ hfr hpar
  obtain ⟨n, hn_le, he⟩ := (Classical.choose_spec hex₀).1
  obtain ⟨hrun, hpr⟩ :=
    simProgInitDet_spec (standardLayout P.input base C.space w)
      (P.initFresh.program P.output) d₀.regs
      (standardLayout_validMem P.input base C.space w _) hd₀.1
      (he.runs (pc := 0) (p := P.initFresh.program P.output) (Program.Contains.self _).append_left)
      (step_halt (i := P.output) (by simp [Code.program])) (Nat.succ_le_succ hn_le)
  refine ⟨hrun, hpr.trans ?_⟩
  rw [standardLayout_spillProbes, ← persistentRegCount_eq_persCount]
  exact Nat.add_le_add_right hn_le _

/-- **Wide-Cell Deterministic Bridge (`WordRAM.StateTransitionImpl.toCellProbeWide`):**
Packs all `persistentRegCount P` persistent registers into `1` wide cell of width
`wideSubroutineWidth P w := max (persistentRegCount P) 1 * w` over `C.space + 1` cells, paying at
most `2` additive probes per operation (`0` when `persistentRegCount P = 0`) regardless of `r_ds`.
-/
noncomputable def toCellProbeWide (C : WordRAM.StateTransitionImpl P D w base params s₀)
    {d₀ : Data r_ds} (hd₀ : d₀.Bounded w)
    (hfr : d₀.regs P.frontierReg = base)
    (hpar : ∀ j, d₀.regs (P.initParams j) = params j) :
    Σ P_cp : Scheme D.Op D.Result (C.space + 1) (wideSubroutineWidth P w),
      { C_cp : Cslib.DataStructure.CellProbe.StateTransitionImpl D P_cp s₀ //
        C_cp.initPotential = C.initPotential ∧
          ∀ s o, C_cp.charge s o =
            C.charge s o + if persistentRegCount P = 0 then 0 else 2 } := by
  let S := C.toCellProbeLayout (wideLayout P.input base C.space w) hd₀ hfr hpar
  refine ⟨S.1, ⟨S.2.1, S.2.2.1, fun s o => (S.2.2.2 s o).trans ?_⟩⟩
  rw [wideLayout_overhead, persistentRegCount_eq_persCount]

end Cslib.DataStructure.WordRAM.StateTransitionImpl

/-! ### 2. Flat `(p_init, p_op)` Las Vegas simulation and contrapositive lower-bound transfer -/

namespace Cslib.DataStructure.CellProbe

universe u v z

/-- Load operation arguments `encode o` into input registers (`input i = true`), preserving
persistent registers (`input i = false`) and all of `x.mem`. -/
@[expose] def prepareFlatRegs {Op : Type*} {r : ℕ} (input : Fin r → Bool)
    (encode : Op → Fin r → ℕ) (o : Op) (x : Data r) : Data r :=
  Data.prepare input (encode o) x

theorem unpack_pack_eq_prepareFlatRegs {Op : Type*} {r S regCells w wCell base : ℕ}
    {input : Fin r → Bool} (L : RegLayout r input base S w regCells wCell)
    (encode : Op → Fin r → ℕ) (o : Op) {x : Data r}
    (hx_bdd : x.Bounded w)
    (hx_out : ∀ a ∉ (Block.mk base S).footprint, x.mem a = 0) :
    L.unpack (encode o) (L.pack x) = prepareFlatRegs input encode o x := by
  ext i
  · exact L.unpack_pack_regs (encode o) hx_bdd i
  · rw [L.unpack_pack_mem (encode o) hx_bdd i]
    dsimp only [prepareFlatRegs, zeroOutside]
    rw [Data.prepare_mem]
    split_ifs with ha
    · rfl
    · exact (hx_out i fun hmem => ha (Block.mem_footprint.mp hmem)).symm

/-- Multi-operation distributional execution of a flat `WordRAM.Program B r` over a deterministic
state-transition specification `D : StateTransitionSpec` (`[D.HasStepFn f]`). -/
inductive ExecFlatProgramOps {B : Basis} {r : ℕ}
    (D : StateTransitionSpec.{u, v, 0})
    {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    (Latent : Type z) (w base space : ℕ)
    (p_op : Program B r) (input : Fin r → Bool)
    (encode : D.Op → Fin r → ℕ)
    (decode : (o : D.Op) → ℕ → (Fin r → ℕ) → Option (D.Result o)) :
    D.State → List D.Op → PMF (Latent × Data r) → PMF (Latent × Data r) → ℝ≥0∞ → Prop where
  | nil (s : D.State) (ν : PMF (Latent × Data r)) :
      ExecFlatProgramOps D Latent w base space p_op input encode decode s [] ν ν 0
  | cons {s : D.State} {o : D.Op} {ops : List D.Op}
      {ν ν_final : PMF (Latent × Data r)}
      {μ_step : Latent × Data r → PMF (Latent × ℕ × Data r)}
      {T_step : Latent × Data r → ℝ≥0∞} {T_rest : ℝ≥0∞} :
      (∀ p ∈ ν.support,
        (∀ i, input i = true → Fits w (encode o i)) ∧
        ExecProgramDist w p_op (prepareFlatRegs input encode o p.2)
          ((μ_step p).map Prod.snd) (T_step p + 1) ∧
        ∀ ℓ outVal y, (ℓ, outVal, y) ∈ (μ_step p).support →
          y.Bounded w ∧
          decode o outVal y.regs = some (D.stepFn s o).2 ∧
          Modifies (Block.mk base space).footprint p.2.mem y.mem) →
      ExecFlatProgramOps D Latent w base space p_op input encode decode (D.stepFn s o).1 ops
        (ν.bind fun p => (μ_step p).map fun ⟨ℓ, _, y⟩ => (ℓ, y)) ν_final T_rest →
      ExecFlatProgramOps D Latent w base space p_op input encode decode s (o :: ops) ν ν_final
        ((∑' p, ν p * T_step p) + T_rest)

private noncomputable def haltedOutputPMF {B : Basis} {r : ℕ} (w : ℕ) (p_op : Program B r)
    (x : Data r) : PMF (ℕ × Data r) :=
  match Classical.propDecidable (HasSum (haltedLim w p_op x) 1) with
  | .isTrue h => ⟨haltedLim w p_op x, h⟩
  | .isFalse _ => PMF.pure (0, x)

private theorem haltedOutputPMF_eq_of_execProgramDist {B : Basis} {r w : ℕ} {p_op : Program B r}
    {x : Data r} {μ : PMF (ℕ × Data r)} {T : ℝ≥0∞}
    (h : ExecProgramDist w p_op x μ T) :
    haltedOutputPMF w p_op x = μ := by
  have heq : haltedLim w p_op x = μ := funext h.haltedLim_eq
  have hsum : HasSum (haltedLim w p_op x) 1 := heq ▸ μ.2
  dsimp only [haltedOutputPMF]
  cases Classical.propDecidable (HasSum (haltedLim w p_op x) 1) with
  | isTrue _ => exact PMF.ext h.haltedLim_eq
  | isFalse hnot => exact absurd hsum hnot

private noncomputable def flatStepDataDist {B : Basis} {r : ℕ} {Op : Type*}
    (w : ℕ) (p_op : Program B r) (input : Fin r → Bool) (encode : Op → Fin r → ℕ)
    (o : Op) (ρ : PMF (Data r)) : PMF (Data r) :=
  ρ.bind fun x =>
    (haltedOutputPMF w p_op (prepareFlatRegs input encode o x)).map Prod.snd

/-- Machine-state distribution `PMF (Data r)` obtained by folding the limiting halting law of `p_op`
over `ops` from initial state distribution `ρ`. On any **certified** `ExecFlatProgramOps` history,
every step halts with mass `1` and this coincides with the exact final `Data r` marginal
(`ExecFlatProgramOps.tighten_actualBodyTime`); on uncertified steps whose halting mass is below `1`
(e.g., an empty program `[]`), a private fallback point mass keeps the transition total. -/
noncomputable def flatStateDist {B : Basis} {r : ℕ} {Op : Type*}
    (w : ℕ) (p_op : Program B r) (input : Fin r → Bool) (encode : Op → Fin r → ℕ) :
    PMF (Data r) → List Op → PMF (Data r)
  | ρ, [] => ρ
  | ρ, o :: ops =>
    flatStateDist w p_op input encode (flatStepDataDist w p_op input encode o ρ) ops

/-- Expected non-`halt` body-instruction count accumulated along `flatStateDist` when running flat
program `p_op` on `ops` from initial state distribution `ρ : PMF (Data r)`. On any **certified**
`ExecFlatProgramOps` history, every step halts with mass `1` and this equals the exact intrinsic
expected body-instruction count (`expectedTime - 1` summed across the exact step marginals,
independent of any caller-supplied time budget `T`, latent variable `Latent`, or proof witness; see
`ExecFlatProgramOps.tighten_actualBodyTime`). On uncertified histories with halting mass below `1`,
subsequent steps advance through the private fallback point mass. -/
noncomputable def flatExpectedBodyTime {B : Basis} {r : ℕ} {Op : Type*}
    (w : ℕ) (p_op : Program B r) (input : Fin r → Bool) (encode : Op → Fin r → ℕ) :
    PMF (Data r) → List Op → ℝ≥0∞
  | _, [] => 0
  | ρ, o :: ops =>
    (∑' x, ρ x * (expectedTime w p_op ⟨0, prepareFlatRegs input encode o x⟩ - 1)) +
      flatExpectedBodyTime w p_op input encode (flatStepDataDist w p_op input encode o ρ) ops

/-- Expected total executed Word-RAM instruction count (including each operation's terminal `halt`
step) accumulated along `flatStateDist` when running `p_op` on `ops` from `ρ : PMF (Data r)`.
Equals the exact total expected executed instruction count on **certified** `ExecFlatProgramOps`
histories (`flatExpectedTime_eq_add_length`); on uncertified histories with halting mass below `1`,
subsequent steps advance through the private fallback point mass. -/
noncomputable def flatExpectedTime {B : Basis} {r : ℕ} {Op : Type*}
    (w : ℕ) (p_op : Program B r) (input : Fin r → Bool) (encode : Op → Fin r → ℕ) :
    PMF (Data r) → List Op → ℝ≥0∞
  | _, [] => 0
  | ρ, o :: ops =>
    (∑' x, ρ x * expectedTime w p_op ⟨0, prepareFlatRegs input encode o x⟩) +
      flatExpectedTime w p_op input encode (flatStepDataDist w p_op input encode o ρ) ops

/-- Running any `WordRAM.Program` from an active state `⟨0, x⟩` takes expected time at least `1`.
-/
theorem one_le_expectedTime {B : Basis} {r : ℕ} (w : ℕ) (p_op : Program B r) (x : Data r) :
    (1 : ℝ≥0∞) ≤ expectedTime w p_op ⟨0, x⟩ := by
  rw [expectedTime_eq_expectedStepsFrom, expectedStepsFrom_running]
  exact le_self_add

/-- Total expected executed instructions (`flatExpectedTime`, including each operation's terminal
`halt` step) equal `flatExpectedBodyTime + ops.length`. -/
theorem flatExpectedTime_eq_add_length {B : Basis} {r : ℕ} {Op : Type*}
    (w : ℕ) (p_op : Program B r) (input : Fin r → Bool) (encode : Op → Fin r → ℕ)
    (ρ : PMF (Data r)) (ops : List Op) :
    flatExpectedTime w p_op input encode ρ ops =
      flatExpectedBodyTime w p_op input encode ρ ops + (ops.length : ℝ≥0∞) := by
  induction ops generalizing ρ with
  | nil => simp [flatExpectedTime, flatExpectedBodyTime]
  | cons o ops ih =>
    simp only [flatExpectedTime, flatExpectedBodyTime, List.length_cons, Nat.cast_add,
      Nat.cast_one, ih]
    rw [tsum_congr fun x => by
        rw [← tsub_add_cancel_of_le (one_le_expectedTime w p_op (prepareFlatRegs input encode o x)),
          mul_add, mul_one],
      tsum_add, ρ.tsum_coe]
    ac_rfl

/-- The non-`halt` body instruction expectation `flatExpectedBodyTime` never exceeds the total
executed instruction expectation `flatExpectedTime`. -/
theorem flatExpectedBodyTime_le_flatExpectedTime {B : Basis} {r : ℕ} {Op : Type*}
    (w : ℕ) (p_op : Program B r) (input : Fin r → Bool) (encode : Op → Fin r → ℕ)
    (ρ : PMF (Data r)) (ops : List Op) :
    flatExpectedBodyTime w p_op input encode ρ ops ≤ flatExpectedTime w p_op input encode ρ ops :=
  (le_self_add).trans_eq (flatExpectedTime_eq_add_length w p_op input encode ρ ops).symm

/-- **Actual-time tightening bridge:** any certified `ExecFlatProgramOps` derivation from `ν` to
`ν_final` with admissible budget `T_ops` also witnesses `ExecFlatProgramOps` with the **exact**
intrinsic expected non-`halt` body-instruction count `flatExpectedBodyTime w p_op input encode
(ν.map Prod.snd) ops` (preserving the exact coupled initial/final distributions `(ν, ν_final)`,
intermediate transitions, and zero-error decode/framing correctness), dominates it
(`flatExpectedBodyTime ... ≤ T_ops`), and evolves the `Data r` marginal along `flatStateDist`. -/
theorem ExecFlatProgramOps.tighten_actualBodyTime {B : Basis} {r w base space : ℕ}
    {D : StateTransitionSpec.{u, v, 0}}
    {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    {Latent : Type z} {p_op : Program B r} {input : Fin r → Bool}
    {encode : D.Op → Fin r → ℕ}
    {decode : (o : D.Op) → ℕ → (Fin r → ℕ) → Option (D.Result o)}
    {s : D.State} {ops : List D.Op} {ν ν_final : PMF (Latent × Data r)} {T_ops : ℝ≥0∞}
    (hex : ExecFlatProgramOps D Latent w base space p_op input encode decode s ops
      ν ν_final T_ops) :
    ExecFlatProgramOps D Latent w base space p_op input encode decode s ops ν ν_final
      (flatExpectedBodyTime w p_op input encode (ν.map Prod.snd) ops) ∧
    flatExpectedBodyTime w p_op input encode (ν.map Prod.snd) ops ≤ T_ops ∧
    ν_final.map Prod.snd = flatStateDist w p_op input encode (ν.map Prod.snd) ops := by
  induction hex with
  | nil s ν => exact ⟨.nil s ν, le_rfl, rfl⟩
  | @cons s o ops_rem ν ν_final μ_step T_step T_rest hstep _ ih =>
    let ν₁ : PMF (Latent × Data r) := ν.bind fun p => (μ_step p).map fun ⟨ℓ, _, y⟩ => (ℓ, y)
    have hmap_eq :
        ν₁.map Prod.snd = flatStepDataDist w p_op input encode o (ν.map Prod.snd) := by
      dsimp only [flatStepDataDist]
      rw [PMF.map_bind, PMF.bind_map]
      refine Probability.PMF.bind_congr_on_support ν _ _ fun p hp => ?_
      dsimp only [Function.comp_def]
      rw [haltedOutputPMF_eq_of_execProgramDist (hstep p hp).2.1, PMF.map_comp, PMF.map_comp]
      rfl
    let t_act : Latent × Data r → ℝ≥0∞ :=
      fun p => expectedTime w p_op ⟨0, prepareFlatRegs input encode o p.2⟩ - 1
    have hstep_act :
        (∑' p, ν p * t_act p) =
          ∑' x, (ν.map Prod.snd) x *
            (expectedTime w p_op ⟨0, prepareFlatRegs input encode o x⟩ - 1) :=
      (Probability.PMF.tsum_map_mul ν Prod.snd
        (fun x => expectedTime w p_op ⟨0, prepareFlatRegs input encode o x⟩ - 1)).symm
    obtain ⟨ih_exec, ih_le, ih_dist⟩ := ih
    refine ⟨?_, ?_, by rw [ih_dist, hmap_eq, flatStateDist]⟩
    · rw [flatExpectedBodyTime, ← hmap_eq, ← hstep_act]
      refine .cons (μ_step := μ_step) (T_step := t_act) (fun p hp => ?_) ih_exec
      obtain ⟨harg, hpd, hpost⟩ := hstep p hp
      exact ⟨harg, ⟨(tsub_add_cancel_of_le (one_le_expectedTime w p_op _)).symm.le,
        hpd.2.1, hpd.2.2⟩, hpost⟩
    · rw [flatExpectedBodyTime, ← hmap_eq, ← hstep_act]
      exact add_le_add (Probability.PMF.tsum_mul_mono_support ν fun p hp =>
        tsub_le_iff_right.mpr (hstep p hp).2.1.1) ih_le

/-- Any admissible `ExecFlatProgramOps` budget `T_ops` dominates the exact expected body-instruction
count `flatExpectedBodyTime w p_op input encode (ν.map Prod.snd) ops`. -/
theorem ExecFlatProgramOps.flatExpectedBodyTime_le {B : Basis} {r w base space : ℕ}
    {D : StateTransitionSpec.{u, v, 0}}
    {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    {Latent : Type z} {p_op : Program B r} {input : Fin r → Bool}
    {encode : D.Op → Fin r → ℕ}
    {decode : (o : D.Op) → ℕ → (Fin r → ℕ) → Option (D.Result o)}
    {s : D.State} {ops : List D.Op} {ν ν_final : PMF (Latent × Data r)} {T_ops : ℝ≥0∞}
    (hex : ExecFlatProgramOps D Latent w base space p_op input encode decode s ops
      ν ν_final T_ops) :
    flatExpectedBodyTime w p_op input encode (ν.map Prod.snd) ops ≤ T_ops :=
  hex.tighten_actualBodyTime.2.1

private theorem ne_top_of_mem_support_of_tsum_ne_top {α : Type*} {ν : PMF α} {f : α → ℝ≥0∞}
    (hsum : (∑' a, ν a * f a) ≠ ⊤) {a : α} (ha : a ∈ ν.support) : f a ≠ ⊤ :=
  fun htop => (ne_top_of_tsum_ne_top hsum a)
    (by rw [htop, ENNReal.mul_top ((PMF.mem_support_iff _ _).mp ha)])

private theorem mem_support_bind_map {α β γ : Type*} {ν : PMF α} {μ : α → PMF β}
    {f : α → β → γ} {a : α} {b : β} (ha : a ∈ ν.support) (hb : b ∈ (μ a).support) :
    f a b ∈ (ν.bind fun a' => (μ a').map (f a')).support :=
  (PMF.mem_support_bind_iff _ _ _).mpr ⟨a, ha, (PMF.mem_support_map_iff _ _ _).mpr ⟨b, hb, rfl⟩⟩

private theorem bounded_zeroOutside_bind_map {α : Type*} {β : Type*} {r w base space : ℕ}
    (ν : PMF α) (μ_step : α → PMF β) (stepState : α → β → α)
    (dataOf : α → Data r) (dataStep : β → Data r)
    (hdata : ∀ a b, dataOf (stepState a b) = dataStep b)
    (hsupp : ∀ a ∈ ν.support,
      (dataOf a).Bounded w ∧ ∀ addr ∉ (Block.mk base space).footprint, (dataOf a).mem addr = 0)
    (hstep_mod : ∀ a ∈ ν.support, ∀ b ∈ (μ_step a).support,
      (dataStep b).Bounded w ∧
        Modifies (Block.mk base space).footprint (dataOf a).mem (dataStep b).mem) :
    ∀ a₁ ∈ (ν.bind fun a => (μ_step a).map (stepState a)).support,
      (dataOf a₁).Bounded w ∧
        ∀ addr ∉ (Block.mk base space).footprint, (dataOf a₁).mem addr = 0 := by
  intro a₁ ha₁
  obtain ⟨a, ha, hb_map⟩ := (PMF.mem_support_bind_iff _ _ _).mp ha₁
  obtain ⟨b, hb, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hb_map
  obtain ⟨hb_bdd, hmod⟩ := hstep_mod a ha b hb
  exact hdata a b ▸ ⟨hb_bdd, fun addr haddr => (hmod addr haddr).trans ((hsupp a ha).2 addr haddr)⟩

private theorem mem_support_runFrom_cons_fst {Op : Type*} {Result : Op → Type}
    {cells wCell : ℕ} (P_cp : Cslib.CellProbe.Randomized.Scheme Op Result cells wCell)
    {m₀ : Mem cells wCell} {o : Op} {ops_rem : List Op}
    {tm : List (Sigma Result) × Mem cells wCell}
    (htm : tm ∈ ((P_cp.runFrom m₀ (o :: ops_rem)).map Prod.fst).support) :
    ∃ z_full ∈ ((P_cp.step o).run m₀).support,
      ∃ tm_rem ∈ ((P_cp.runFrom z_full.1.2 ops_rem).map Prod.fst).support,
        tm = (⟨o, z_full.1.1⟩ :: tm_rem.1, tm_rem.2) := by
  rw [P_cp.runFrom_cons_fst, PMF.mem_support_bind_iff] at htm
  obtain ⟨_, hz₁, htm_rem⟩ := htm
  obtain ⟨z_full, hz_full, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hz₁
  obtain ⟨tm_rem, htm_rem_mem, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp htm_rem
  exact ⟨z_full, hz_full, tm_rem, htm_rem_mem, rfl⟩

private theorem mem_support_map_fst_runSeq_of_map {Op : Type*} {Result : Op → Type}
    {cells wCell : ℕ} {α : Type*}
    (P_cp : Cslib.CellProbe.Randomized.Scheme Op Result cells wCell)
    {ν₀ : PMF α} {packOf : α → Mem cells wCell} (hinit : P_cp.init = ν₀.map packOf)
    {ops : List Op} {tr : List (Sigma Result)}
    (htr : tr ∈ ((P_cp.runSeq ops).map Prod.fst).support) :
    ∃ a ∈ ν₀.support, ∃ m_fin,
      (tr, m_fin) ∈ ((P_cp.runFrom (packOf a) ops).map Prod.fst).support := by
  rw [Cslib.CellProbe.Randomized.Scheme.runSeq, hinit, PMF.map_bind,
    PMF.mem_support_bind_iff] at htr
  obtain ⟨_, hm₀, htr_from⟩ := htr
  obtain ⟨a, ha, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hm₀
  rw [PMF.map_comp, PMF.mem_support_map_iff] at htr_from
  obtain ⟨⟨⟨tr', m_fin⟩, pr⟩, htm, rfl⟩ := htr_from
  exact ⟨a, ha, m_fin, (PMF.mem_support_map_iff _ _ _).mpr ⟨((tr', m_fin), pr), htm, rfl⟩⟩

private theorem tsum_expectedProbesFrom_cons_le {Op : Type*} {Result : Op → Type}
    {cells wCell : ℕ} {α : Type*} {β : Type*}
    (P_cp : Cslib.CellProbe.Randomized.Scheme Op Result cells wCell)
    (ν : PMF α) (μ_step : α → PMF β) (stepState : α → β → α)
    (memOf : α → Mem cells wCell) (T_step : α → ℝ≥0∞) (ov T_rest : ℝ≥0∞)
    (o : Op) (ops_rem : List Op)
    (hexp_rem :
      (∑' a₁, (ν.bind fun a => (μ_step a).map (stepState a)) a₁ *
          P_cp.expectedProbesFrom (memOf a₁) ops_rem) ≤
        T_rest + ov * (ops_rem.length : ℝ≥0∞))
    (hpt_supp : ∀ a ∈ ν.support,
      P_cp.expectedProbesFrom (memOf a) (o :: ops_rem) ≤
        T_step a + ov +
          ∑' b, μ_step a b * P_cp.expectedProbesFrom (memOf (stepState a b)) ops_rem) :
    (∑' a, ν a * P_cp.expectedProbesFrom (memOf a) (o :: ops_rem)) ≤
      ((∑' a, ν a * T_step a) + T_rest) + ov * ((o :: ops_rem).length : ℝ≥0∞) := by
  have hbind_eq :
      (∑' a, ν a * ∑' b, μ_step a b * P_cp.expectedProbesFrom (memOf (stepState a b)) ops_rem) =
        ∑' a₁, (ν.bind fun a => (μ_step a).map (stepState a)) a₁ *
          P_cp.expectedProbesFrom (memOf a₁) ops_rem := by
    rw [Probability.PMF.tsum_bind_mul]
    refine tsum_congr fun a => congrArg (ν a * ·) (Probability.PMF.tsum_map_mul (μ_step a)
      (stepState a) (fun a₁ => P_cp.expectedProbesFrom (memOf a₁) ops_rem)).symm
  refine (Probability.PMF.tsum_mul_mono_support ν hpt_supp).trans ?_
  simp only [mul_add, add_assoc]
  rw [tsum_add, tsum_add, ENNReal.tsum_mul_right, ν.tsum_coe, one_mul, hbind_eq, ← add_assoc]
  exact (add_le_add le_rfl hexp_rem).trans_eq (by
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]; ring)

private theorem lasVegas_cons_step {B : Basis} {r regCells wCell w base space : ℕ}
    {input : Fin r → Bool} {Op : Type*} {Result : Op → Type} {o : Op}
    (L : RegLayout r input base space w regCells wCell)
    (P_cp : Cslib.CellProbe.Randomized.Scheme Op Result (space + regCells) wCell)
    (p_op : Program B r) (encode : Op → Fin r → ℕ)
    (decode : ℕ → (Fin r → ℕ) → Option (Result o)) (dflt : Result o) (K M_corr : ℕ) (η : ℝ≥0∞)
    (hstep_eq : P_cp.step o = simProgRand (w := w) L p_op (encode o) decode dflt K)
    (hW_step : ∀ o' m, (P_cp.step o').expectedProbes m ≤
      ((K + 2 * space + regCells + L.overhead : ℕ) : ℝ≥0∞))
    {ops_rem : List Op} (hlen_rem : ops_rem.length ≤ M_corr)
    {x : Data r} {μ_vy : PMF (ℕ × Data r)} {T_p : ℝ≥0∞}
    (hx_bdd : x.Bounded w) (hx_out : ∀ a ∉ (Block.mk base space).footprint, x.mem a = 0)
    (harg : ∀ i, input i = true → Fits w (encode o i))
    (hTp_fin : T_p ≠ ⊤)
    (hpdist : ExecProgramDist w p_op (prepareFlatRegs input encode o x) μ_vy (T_p + 1))
    (hK_tail_o : ∀ m : Mem (space + regCells) wCell,
      (∃ μ_p : PMF (ℕ × Data r), ∃ T' : ℝ≥0∞, T' ≠ ⊤ ∧
        ExecProgramDist w p_op (L.unpack (encode o) m) μ_p (T' + 1)) →
      (evalRand w p_op K ⟨0, L.unpack (encode o) m⟩).toOuterMeasure (RandCfg.runningSet r) *
        ((((2 * space + regCells) + M_corr * (2 * space + regCells + L.overhead) : ℕ) : ℝ≥0∞) +
          (M_corr : ℝ≥0∞) * (K : ℝ≥0∞)) ≤ η) :
    (∀ tm ∈ ((P_cp.runFrom (L.pack x) (o :: ops_rem)).map Prod.fst).support,
      ∃ vy ∈ μ_vy.support, ∃ tm_rem ∈ ((P_cp.runFrom (L.pack vy.2) ops_rem).map Prod.fst).support,
        tm = (⟨o, (decode vy.1 vy.2.regs).getD dflt⟩ :: tm_rem.1, tm_rem.2)) ∧
    P_cp.expectedProbesFrom (L.pack x) (o :: ops_rem) ≤
      T_p + ((L.overhead : ℝ≥0∞) + η) +
        ∑' vy, μ_vy vy * P_cp.expectedProbesFrom (L.pack vy.2) ops_rem := by
  rw [← unpack_pack_eq_prepareFlatRegs L encode o hx_bdd hx_out] at hpdist
  obtain ⟨hsup_sim, hexp_sim, hcoupl⟩ :=
    simProgRand_lasVegas_spec L p_op (encode o) decode dflt K (L.validMem_pack x) harg hpdist
  rw [← hstep_eq] at hsup_sim hexp_sim hcoupl
  refine ⟨fun tm htm => ?_, ?_⟩
  · obtain ⟨z_full, hz_full, tm_rem, htm_rem, rfl⟩ := mem_support_runFrom_cons_fst P_cp htm
    obtain ⟨vy, hvy, hz_eq⟩ := hsup_sim z_full hz_full
    have hz1 : z_full.1.1 = (decode vy.1 vy.2.regs).getD dflt := congrArg Prod.fst hz_eq
    have hz2 : z_full.1.2 = L.pack vy.2 := congrArg Prod.snd hz_eq
    exact ⟨vy, hvy, tm_rem, hz2 ▸ htm_rem, hz1 ▸ rfl⟩
  · set W_step : ℝ≥0∞ := ((K + 2 * space + regCells + L.overhead : ℕ) : ℝ≥0∞)
    set B_rem : ℝ≥0∞ := (M_corr : ℝ≥0∞) * W_step
    have hg_bound : ∀ om ∈ (((P_cp.step o).run (L.pack x)).map Prod.fst).support,
        P_cp.expectedProbesFrom om.2 ops_rem ≤ B_rem := fun om _ =>
      (expectedProbesFrom_le_mul P_cp W_step hW_step ops_rem om.2).trans
        (mul_le_mul' (Nat.cast_le.mpr hlen_rem) le_rfl)
    set p_run := (evalRand w p_op K ⟨0, L.unpack (encode o) (L.pack x)⟩).toOuterMeasure
      (RandCfg.runningSet r)
    have htail_le : p_run * (((2 * space + regCells : ℕ) : ℝ≥0∞) + B_rem) ≤ η := by
      rw [show ((2 * space + regCells : ℕ) : ℝ≥0∞) + B_rem =
        (((2 * space + regCells) + M_corr * (2 * space + regCells + L.overhead) : ℕ) : ℝ≥0∞) +
          (M_corr : ℝ≥0∞) * (K : ℝ≥0∞) by dsimp [B_rem, W_step]; push_cast; ring]
      exact hK_tail_o (L.pack x) ⟨μ_vy, T_p, hTp_fin, hpdist⟩
    rw [P_cp.expectedProbesFrom_cons]
    have hstep_le : (P_cp.step o).expectedProbes (L.pack x) ≤
        T_p + (L.overhead : ℝ≥0∞) + p_run * ((2 * space + regCells : ℕ) : ℝ≥0∞) :=
      hexp_sim.trans (add_le_add (add_le_add
        (continuing_sum_le_of_almostSurelyHalts hpdist.almostSurelyHalts hpdist.1 K) le_rfl) le_rfl)
    refine (add_le_add hstep_le
      (hcoupl (fun om => P_cp.expectedProbesFrom om.2 ops_rem) B_rem hg_bound)).trans ?_
    calc (T_p + (L.overhead : ℝ≥0∞) + p_run * ((2 * space + regCells : ℕ) : ℝ≥0∞)) +
          ((∑' vy, μ_vy vy * P_cp.expectedProbesFrom (L.pack vy.2) ops_rem) + p_run * B_rem)
      _ = T_p + (L.overhead : ℝ≥0∞) +
            (∑' vy, μ_vy vy * P_cp.expectedProbesFrom (L.pack vy.2) ops_rem) +
            p_run * (((2 * space + regCells : ℕ) : ℝ≥0∞) + B_rem) := by ring
      _ ≤ _ := (add_le_add le_rfl htail_le).trans_eq (by ac_rfl)

private theorem exists_uniform_cutoff_singleProg {B : Basis}
    {r regCells wCell w base space : ℕ} {input : Fin r → Bool} {Op : Type*}
    (L : RegLayout r input base space w regCells wCell)
    (opsAlphabet : Finset Op) (p_op : Program B r) (encode : Op → Fin r → ℕ)
    (M_corr : ℕ) {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ K : ℕ, ∀ o ∈ opsAlphabet, ∀ m : Mem (space + regCells) wCell,
      (∃ μ_p : PMF (ℕ × Data r), ∃ T_p : ℝ≥0∞, T_p ≠ ⊤ ∧
        ExecProgramDist w p_op (L.unpack (encode o) m) μ_p (T_p + 1)) →
      (evalRand w p_op K ⟨0, L.unpack (encode o) m⟩).toOuterMeasure (RandCfg.runningSet r) *
        ((((2 * space + regCells) + M_corr * (2 * space + regCells + L.overhead) : ℕ) : ℝ≥0∞) +
          (M_corr : ℝ≥0∞) * (K : ℝ≥0∞)) ≤ η := by
  let Good : Op → Mem (space + regCells) wCell → Prop := fun o m =>
    ∃ μ_p : PMF (ℕ × Data r), ∃ T_p : ℝ≥0∞, T_p ≠ ⊤ ∧
      ExecProgramDist w p_op (L.unpack (encode o) m) μ_p (T_p + 1)
  obtain ⟨K, _, hK_tail⟩ := exists_uniform_cutoff L opsAlphabet Good (fun _ => p_op) encode
    (fun o _ m ⟨_, _, hTp, hd⟩ =>
      ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hTp, ENNReal.one_ne_top⟩) hd.1)
    ((2 * space + regCells) + M_corr * (2 * space + regCells + L.overhead)) M_corr hη
  exact ⟨K, hK_tail⟩

private theorem simFlatOps_induction {B : Basis} {r regCells wCell w base space : ℕ}
    {D : StateTransitionSpec.{u, v, 0}}
    {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    [∀ o, Inhabited (D.Result o)]
    {Latent : Type z} {p_op : Program B r} {input : Fin r → Bool}
    {encode : D.Op → Fin r → ℕ}
    {decode : (o : D.Op) → ℕ → (Fin r → ℕ) → Option (D.Result o)}
    (L : RegLayout r input base space w regCells wCell)
    (initMem : PMF (Mem (space + regCells) wCell))
    (opsAlphabet : Finset D.Op) (M_corr : ℕ) (K : ℕ) (η : ℝ≥0∞)
    (hK_tail : ∀ o ∈ opsAlphabet, ∀ m : Mem (space + regCells) wCell,
      (∃ μ_p : PMF (ℕ × Data r), ∃ T_p : ℝ≥0∞, T_p ≠ ⊤ ∧
        ExecProgramDist w p_op (L.unpack (encode o) m) μ_p (T_p + 1)) →
      (evalRand w p_op K ⟨0, L.unpack (encode o) m⟩).toOuterMeasure (RandCfg.runningSet r) *
        ((((2 * space + regCells) + M_corr * (2 * space + regCells + L.overhead) : ℕ) : ℝ≥0∞) +
          (M_corr : ℝ≥0∞) * (K : ℝ≥0∞)) ≤ η)
    {s : D.State} {ops : List D.Op} {ν ν_final : PMF (Latent × Data r)} {T_ops : ℝ≥0∞}
    (hex : ExecFlatProgramOps D Latent w base space p_op input encode decode s ops ν ν_final T_ops)
    (hlen : ops.length ≤ M_corr)
    (halph : ∀ o ∈ ops, o ∈ opsAlphabet)
    (hT_fin : T_ops ≠ ⊤)
    (hsupp : ∀ p ∈ ν.support,
      p.2.Bounded w ∧ ∀ a ∉ (Block.mk base space).footprint, p.2.mem a = 0) :
    let P_cp : Cslib.CellProbe.Randomized.Scheme D.Op D.Result (space + regCells) wCell :=
      { init := initMem
        step := fun o =>
          simProgRand (w := w) L p_op (encode o) (decode o) default K }
    (∀ p ∈ ν.support, ∀ tm ∈ ((P_cp.runFrom (L.pack p.2) ops).map Prod.fst).support,
      tm.1 = (D.run s ops).2) ∧
    (∑' p, ν p * P_cp.expectedProbesFrom (L.pack p.2) ops) ≤
      T_ops + ((L.overhead : ℝ≥0∞) + η) * (ops.length : ℝ≥0∞) := by
  intro P_cp
  have hW_step : ∀ o' m, (P_cp.step o').expectedProbes m ≤
      ((K + 2 * space + regCells + L.overhead : ℕ) : ℝ≥0∞) := fun o' m =>
    simProgRand_expectedProbes_le_worstCase L p_op (encode o') (decode o') default K m
  induction hex with
  | nil s ν =>
    refine ⟨fun p _ tm htm => ?_, by simp [Cslib.CellProbe.Randomized.Scheme.expectedProbesFrom]⟩
    simp only [Cslib.CellProbe.Randomized.Scheme.runFrom, PMF.pure_map, PMF.support_pure,
      Set.mem_singleton_iff] at htm
    rw [htm, StateTransitionSpec.run_nil]
  | @cons s o ops_rem ν ν_final μ_step T_step T_rest hstep _ ih =>
    have hsum_fin : (∑' p, ν p * T_step p) ≠ ⊤ := ne_top_of_le_ne_top hT_fin le_self_add
    have hsupp₁ := bounded_zeroOutside_bind_map ν μ_step (fun _ q => (q.1, q.2.2)) Prod.snd
      (fun q => q.2.2) (fun _ _ => rfl) hsupp fun p hp q hq =>
        ⟨((hstep p hp).2.2 q.1 q.2.1 q.2.2 hq).1, ((hstep p hp).2.2 q.1 q.2.1 q.2.2 hq).2.2⟩
    obtain ⟨hcorr_rem, hexp_rem⟩ := ih (Nat.le_of_succ_le hlen)
      (fun o' ho' => halph o' (List.mem_cons_of_mem o ho'))
      (ne_top_of_le_ne_top hT_fin le_add_self) hsupp₁
    have hstep_cp := fun p (hp : p ∈ ν.support) =>
      lasVegas_cons_step L P_cp p_op encode (decode o) (default : D.Result o) K M_corr η rfl
        hW_step (Nat.le_of_succ_le hlen) (hsupp p hp).1 (hsupp p hp).2 (hstep p hp).1
        (ne_top_of_mem_support_of_tsum_ne_top hsum_fin hp) (hstep p hp).2.1
        (hK_tail o (halph o List.mem_cons_self))
    refine ⟨?_, ?_⟩
    · intro p hp tm htm
      obtain ⟨vy, hvy, tm_rem, htm_rem, rfl⟩ := (hstep_cp p hp).1 tm htm
      obtain ⟨q, hq, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hvy
      simp [StateTransitionSpec.run_cons, ((hstep p hp).2.2 q.1 q.2.1 q.2.2 hq).2.1,
        hcorr_rem (q.1, q.2.2) (mem_support_bind_map hp hq) tm_rem htm_rem]
    · refine tsum_expectedProbesFrom_cons_le P_cp ν μ_step (fun _ q => (q.1, q.2.2))
        (fun p => L.pack p.2) T_step ((L.overhead : ℝ≥0∞) + η) T_rest o ops_rem hexp_rem
        fun p hp => ?_
      simpa only [Probability.PMF.tsum_map_mul (μ_step p) Prod.snd] using (hstep_cp p hp).2

/-- Uniform layout-parametric cell-probe simulation of a flat `(ν₀, p_op)` Las Vegas Word-RAM
program pair: constructs a single `P_cp` **outside** `∀ ops` that is 100% zero-error on all
histories over `opsAlphabet` of length `≤ M_corr` admitting a finite-time `ExecFlatProgramOps`
derivation, with `P_cp.expectedSeqProbes ops ≤ T_ops + (L.overhead + η) * ops.length`. -/
theorem exists_cellProbeLayout_of_flatPrograms {B : Basis} {r regCells wCell w base space : ℕ}
    {input : Fin r → Bool}
    {D : StateTransitionSpec.{u, v, 0}}
    {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    [∀ o, Inhabited (D.Result o)]
    {Latent : Type z} (s₀ : D.State)
    (L : RegLayout r input base space w regCells wCell)
    (p_op : Program B r) (encode : D.Op → Fin r → ℕ)
    (decode : (o : D.Op) → ℕ → (Fin r → ℕ) → Option (D.Result o))
    (ν₀ : PMF (Latent × Data r))
    (hsupp₀ : ∀ p ∈ ν₀.support,
      p.2.Bounded w ∧ ∀ a ∉ (Block.mk base space).footprint, p.2.mem a = 0)
    (opsAlphabet : Finset D.Op) (M_corr : ℕ) {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ P_cp : Cslib.CellProbe.Randomized.Scheme D.Op D.Result (space + regCells) wCell,
      ∀ (ops : List D.Op) {ν_final : PMF (Latent × Data r)} {T_ops : ℝ≥0∞},
        D.ValidHistory s₀ ops →
        ops.length ≤ M_corr →
        (∀ o ∈ ops, o ∈ opsAlphabet) →
        T_ops ≠ ⊤ →
        ExecFlatProgramOps D Latent w base space p_op input encode decode s₀ ops ν₀ ν_final T_ops →
        (D.toObliviousSequenceSpec s₀).Contract ops ((P_cp.runSeq ops).map Prod.fst) ∧
          P_cp.expectedSeqProbes ops ≤
            T_ops + ((L.overhead : ℝ≥0∞) + η) * (ops.length : ℝ≥0∞) := by
  obtain ⟨K, hK_tail⟩ := exists_uniform_cutoff_singleProg L opsAlphabet p_op encode M_corr hη
  let P_cp : Cslib.CellProbe.Randomized.Scheme D.Op D.Result (space + regCells) wCell :=
    { init := ν₀.map fun p => L.pack p.2
      step := fun o => simProgRand (w := w) L p_op (encode o) (decode o) default K }
  refine ⟨P_cp, fun ops {ν_final T_ops} hv hlen halph hT_fin hex => ?_⟩
  obtain ⟨hcorr, hexp⟩ := simFlatOps_induction L (ν₀.map fun p => L.pack p.2) opsAlphabet
    M_corr K η hK_tail hex hlen halph hT_fin hsupp₀
  refine ⟨(D.toObliviousSequenceSpec_contract_iff_of_hasStepFn s₀ hv _).mpr fun tr htr => ?_, ?_⟩
  · obtain ⟨p, hp, m_fin, htm⟩ := mem_support_map_fst_runSeq_of_map P_cp rfl htr
    exact hcorr p hp (tr, m_fin) htm
  · rwa [Cslib.CellProbe.Randomized.Scheme.expectedSeqProbes_eq_init_tsum,
      Probability.PMF.tsum_map_mul]

/-- Standard `w`-bit cell-probe simulation of a flat `(ν₀, p_op)` Las Vegas Word-RAM program pair
over `space + persCount input` cells (`0` extra cells and `0` overhead when `∀ i, input i = true`).
-/
theorem exists_cellProbe_of_flatPrograms {B : Basis} {r w base space : ℕ} {input : Fin r → Bool}
    {D : StateTransitionSpec.{u, v, 0}}
    {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    [∀ o, Inhabited (D.Result o)]
    {Latent : Type z} (s₀ : D.State)
    (p_op : Program B r) (encode : D.Op → Fin r → ℕ)
    (decode : (o : D.Op) → ℕ → (Fin r → ℕ) → Option (D.Result o))
    (ν₀ : PMF (Latent × Data r))
    (hsupp₀ : ∀ p ∈ ν₀.support,
      p.2.Bounded w ∧ ∀ a ∉ (Block.mk base space).footprint, p.2.mem a = 0)
    (opsAlphabet : Finset D.Op) (M_corr : ℕ) {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ P_cp : Cslib.CellProbe.Randomized.Scheme D.Op D.Result (space + persCount input) w,
      ∀ (ops : List D.Op) {ν_final : PMF (Latent × Data r)} {T_ops : ℝ≥0∞},
        D.ValidHistory s₀ ops →
        ops.length ≤ M_corr →
        (∀ o ∈ ops, o ∈ opsAlphabet) →
        T_ops ≠ ⊤ →
        ExecFlatProgramOps D Latent w base space p_op input encode decode s₀ ops ν₀ ν_final T_ops →
        (D.toObliviousSequenceSpec s₀).Contract ops ((P_cp.runSeq ops).map Prod.fst) ∧
          P_cp.expectedSeqProbes ops ≤
            T_ops + (((2 * persCount input : ℕ) : ℝ≥0∞) + η) * (ops.length : ℝ≥0∞) := by
  simpa only [standardLayout_overhead] using
    exists_cellProbeLayout_of_flatPrograms s₀ (standardLayout input base space w) p_op encode
      decode ν₀ hsupp₀ opsAlphabet M_corr hη

/-- Wide-cell (`space + 1` cells of width `wideWidth input w`) simulation of a flat `(ν₀, p_op)`
Las Vegas Word-RAM program pair (`≤ 2` additive probes per operation regardless of `r`). -/
theorem exists_cellProbeWide_of_flatPrograms {B : Basis} {r w base space : ℕ}
    {input : Fin r → Bool}
    {D : StateTransitionSpec.{u, v, 0}}
    {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    [∀ o, Inhabited (D.Result o)]
    {Latent : Type z} (s₀ : D.State)
    (p_op : Program B r) (encode : D.Op → Fin r → ℕ)
    (decode : (o : D.Op) → ℕ → (Fin r → ℕ) → Option (D.Result o))
    (ν₀ : PMF (Latent × Data r))
    (hsupp₀ : ∀ p ∈ ν₀.support,
      p.2.Bounded w ∧ ∀ a ∉ (Block.mk base space).footprint, p.2.mem a = 0)
    (opsAlphabet : Finset D.Op) (M_corr : ℕ) {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ P_cp :
        Cslib.CellProbe.Randomized.Scheme D.Op D.Result (space + 1) (wideWidth input w),
      ∀ (ops : List D.Op) {ν_final : PMF (Latent × Data r)} {T_ops : ℝ≥0∞},
        D.ValidHistory s₀ ops →
        ops.length ≤ M_corr →
        (∀ o ∈ ops, o ∈ opsAlphabet) →
        T_ops ≠ ⊤ →
        ExecFlatProgramOps D Latent w base space p_op input encode decode s₀ ops ν₀ ν_final T_ops →
        (D.toObliviousSequenceSpec s₀).Contract ops ((P_cp.runSeq ops).map Prod.fst) ∧
          P_cp.expectedSeqProbes ops ≤
            T_ops + (((if persCount input = 0 then 0 else 2 : ℕ) : ℝ≥0∞) + η) *
              (ops.length : ℝ≥0∞) := by
  simpa only [wideLayout_overhead] using
    exists_cellProbeLayout_of_flatPrograms s₀ (wideLayout input base space w) p_op encode decode
      ν₀ hsupp₀ opsAlphabet M_corr hη

private theorem lower_bound_of_exists_cellProbeLayout
    {D : StateTransitionSpec.{u, v, 0}}
    {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    (s₀ : D.State) {cells wCell S_max : ℕ} (hspace : cells ≤ S_max)
    (opsAlphabet : Finset D.Op) (M_corr : ℕ)
    (correctSeqs : Set (List D.Op))
    (hcorrectSeqs : ∀ ops ∈ correctSeqs,
      D.ValidHistory s₀ ops ∧ ops.length ≤ M_corr ∧ ∀ o ∈ ops, o ∈ opsAlphabet)
    (hardDist : PMF (List D.Op))
    (hhardDist : ∀ ops ∈ hardDist.support,
      D.ValidHistory s₀ ops ∧ ops.length ≤ M_corr ∧ ∀ o ∈ ops, o ∈ opsAlphabet)
    (initPot : ℝ≥0∞) (timeBound : List D.Op → ℝ≥0∞) (ovBound : ℝ≥0∞)
    (hsim : ∀ [∀ o, Inhabited (D.Result o)] (η : ℝ≥0∞), 0 < η →
      ∃ P_raw : Cslib.CellProbe.Randomized.Scheme D.Op D.Result cells wCell,
        (∀ ops ∈ correctSeqs,
          (D.toObliviousSequenceSpec s₀).Contract ops ((P_raw.runSeq ops).map Prod.fst)) ∧
        (∀ ops ∈ hardDist.support,
          P_raw.expectedSeqProbes ops ≤
            initPot + timeBound ops + (ovBound + η) * (ops.length : ℝ≥0∞)))
    {LB : ℝ≥0∞}
    (hlb : ∀ D_det : IndexedScheme D.Op D.Result S_max wCell,
      (∀ ops ∈ correctSeqs, (D_det.runSeq ops).1 = (D.run s₀ ops).2) →
      LB ≤ ∑' ops, hardDist ops * (D_det.seqProbes ops : ℝ≥0∞)) :
    LB ≤ initPot + ∑' ops, hardDist ops * (timeBound ops + ovBound * (ops.length : ℝ≥0∞)) := by
  classical
  have _ : ∀ o, Inhabited (D.Result o) := fun o => ⟨(f s₀ o).2⟩
  refine le_of_forall_pos_le_add_mul (M := M_corr) fun {η} hη => ?_
  obtain ⟨P_raw, hcorr_raw, hexp_raw⟩ := hsim η hη
  let P_pad := P_raw.padCells hspace
  have hcorr_pad : ∀ ops ∈ correctSeqs,
      (D.toObliviousSequenceSpec s₀).Contract ops ((P_pad.runSeq ops).map Prod.fst) := fun ops h =>
    (P_raw.runSeq_padCells hspace ops).symm ▸ hcorr_raw ops h
  obtain ⟨D_det, _, hD_corr, hD_probes⟩ :=
    Cslib.DataStructure.CellProbe.Randomized.exists_det_indexedScheme_le_expectedSeqProbes
      s₀ P_pad opsAlphabet M_corr correctSeqs hcorrectSeqs hcorr_pad hardDist
      (fun ops hops => (hhardDist ops hops).2)
  refine (hlb D_det hD_corr).trans (hD_probes.trans ?_)
  refine (Probability.PMF.tsum_mul_mono_support hardDist
    (g := fun ops =>
      initPot + (timeBound ops + ovBound * (ops.length : ℝ≥0∞)) + η * (M_corr : ℝ≥0∞))
    fun ops hops => ?_).trans ?_
  · rw [Cslib.CellProbe.Randomized.Scheme.expectedSeqProbes_padCells]
    exact ((hexp_raw ops hops).trans_eq (by ring)).trans
      (add_le_add le_rfl (mul_le_mul' le_rfl (Nat.cast_le.mpr (hhardDist ops hops).2.1)))
  · simp only [mul_add]
    rw [tsum_add, tsum_add, ENNReal.tsum_mul_right, ENNReal.tsum_mul_right,
      hardDist.tsum_coe, one_mul, one_mul, add_assoc]

/-- **Contrapositive Word-RAM lower-bound transfer for flat `(ν₀, p_op)` programs** (standard
`w`-bit cell layout over `S_max ≥ space + persCount input` cells, `0` `η`-loss, no
`[Fintype D.Op]`). -/
theorem flat_wordRAM_lower_bound_of_det_cellProbe {B : Basis} {r w base space S_max : ℕ}
    {input : Fin r → Bool}
    {D : StateTransitionSpec.{u, v, 0}}
    {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    {Latent : Type z} (s₀ : D.State)
    (hspace : space + persCount input ≤ S_max)
    (p_op : Program B r) (encode : D.Op → Fin r → ℕ)
    (decode : (o : D.Op) → ℕ → (Fin r → ℕ) → Option (D.Result o))
    (ν₀ : PMF (Latent × Data r))
    (hsupp₀ : ∀ p ∈ ν₀.support,
      p.2.Bounded w ∧ ∀ a ∉ (Block.mk base space).footprint, p.2.mem a = 0)
    (opsAlphabet : Finset D.Op) (M_corr : ℕ)
    (correctSeqs : Set (List D.Op))
    (hcorrectSeqs : ∀ ops ∈ correctSeqs,
      D.ValidHistory s₀ ops ∧ ops.length ≤ M_corr ∧ ∀ o ∈ ops, o ∈ opsAlphabet)
    (hex_corr : ∀ ops ∈ correctSeqs, ∃ ν_final T_ops, T_ops ≠ ⊤ ∧
      ExecFlatProgramOps D Latent w base space p_op input encode decode s₀ ops ν₀ ν_final T_ops)
    (hardDist : PMF (List D.Op))
    (hhardDist : ∀ ops ∈ hardDist.support,
      D.ValidHistory s₀ ops ∧ ops.length ≤ M_corr ∧ ∀ o ∈ ops, o ∈ opsAlphabet)
    (timeBound : List D.Op → ℝ≥0∞)
    (hex_hard : ∀ ops ∈ hardDist.support, ∃ ν_final T_ops,
      T_ops ≤ timeBound ops ∧ T_ops ≠ ⊤ ∧
      ExecFlatProgramOps D Latent w base space p_op input encode decode s₀ ops ν₀ ν_final T_ops)
    {LB : ℝ≥0∞}
    (hlb : ∀ D_det : IndexedScheme D.Op D.Result S_max w,
      (∀ ops ∈ correctSeqs, (D_det.runSeq ops).1 = (D.run s₀ ops).2) →
      LB ≤ ∑' ops, hardDist ops * (D_det.seqProbes ops : ℝ≥0∞)) :
    LB ≤ ∑' ops, hardDist ops *
      (timeBound ops + ((2 * persCount input : ℕ) : ℝ≥0∞) * (ops.length : ℝ≥0∞)) := by
  rw [← zero_add (∑' ops, _)]
  exact lower_bound_of_exists_cellProbeLayout s₀ hspace opsAlphabet M_corr correctSeqs
    hcorrectSeqs hardDist hhardDist 0 timeBound _ (fun _ hη =>
      let ⟨P_raw, hP⟩ := exists_cellProbe_of_flatPrograms s₀ p_op encode decode ν₀ hsupp₀
        opsAlphabet M_corr hη
      ⟨P_raw,
        fun ops h =>
          let ⟨hv, hl, ha⟩ := hcorrectSeqs ops h
          let ⟨_, _, hf, hx⟩ := hex_corr ops h
          (hP ops hv hl ha hf hx).1,
        fun ops h => by
          obtain ⟨hv, hl, ha⟩ := hhardDist ops h
          obtain ⟨_, _, hT, hf, hx⟩ := hex_hard ops h
          simpa only [zero_add] using (hP ops hv hl ha hf hx).2.trans (add_le_add hT le_rfl)⟩) hlb

/-- **Wide-cell contrapositive Word-RAM lower-bound transfer for flat `(ν₀, p_op)` programs**
(`S_max ≥ space + 1` cells of width `wideWidth input w`, `≤ 2` additive probes per operation
regardless of `r`, `0` `η`-loss, no `[Fintype D.Op]`). -/
theorem flat_wordRAM_lower_bound_of_det_cellProbe_wide {B : Basis} {r w base space S_max : ℕ}
    {input : Fin r → Bool}
    {D : StateTransitionSpec.{u, v, 0}}
    {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    {Latent : Type z} (s₀ : D.State)
    (hspace : space + 1 ≤ S_max)
    (p_op : Program B r) (encode : D.Op → Fin r → ℕ)
    (decode : (o : D.Op) → ℕ → (Fin r → ℕ) → Option (D.Result o))
    (ν₀ : PMF (Latent × Data r))
    (hsupp₀ : ∀ p ∈ ν₀.support,
      p.2.Bounded w ∧ ∀ a ∉ (Block.mk base space).footprint, p.2.mem a = 0)
    (opsAlphabet : Finset D.Op) (M_corr : ℕ)
    (correctSeqs : Set (List D.Op))
    (hcorrectSeqs : ∀ ops ∈ correctSeqs,
      D.ValidHistory s₀ ops ∧ ops.length ≤ M_corr ∧ ∀ o ∈ ops, o ∈ opsAlphabet)
    (hex_corr : ∀ ops ∈ correctSeqs, ∃ ν_final T_ops, T_ops ≠ ⊤ ∧
      ExecFlatProgramOps D Latent w base space p_op input encode decode s₀ ops ν₀ ν_final T_ops)
    (hardDist : PMF (List D.Op))
    (hhardDist : ∀ ops ∈ hardDist.support,
      D.ValidHistory s₀ ops ∧ ops.length ≤ M_corr ∧ ∀ o ∈ ops, o ∈ opsAlphabet)
    (timeBound : List D.Op → ℝ≥0∞)
    (hex_hard : ∀ ops ∈ hardDist.support, ∃ ν_final T_ops,
      T_ops ≤ timeBound ops ∧ T_ops ≠ ⊤ ∧
      ExecFlatProgramOps D Latent w base space p_op input encode decode s₀ ops ν₀ ν_final T_ops)
    {LB : ℝ≥0∞}
    (hlb : ∀ D_det : IndexedScheme D.Op D.Result S_max (wideWidth input w),
      (∀ ops ∈ correctSeqs, (D_det.runSeq ops).1 = (D.run s₀ ops).2) →
      LB ≤ ∑' ops, hardDist ops * (D_det.seqProbes ops : ℝ≥0∞)) :
    LB ≤ ∑' ops, hardDist ops *
      (timeBound ops +
        ((if persCount input = 0 then 0 else 2 : ℕ) : ℝ≥0∞) * (ops.length : ℝ≥0∞)) := by
  rw [← zero_add (∑' ops, _)]
  exact lower_bound_of_exists_cellProbeLayout s₀ hspace opsAlphabet M_corr correctSeqs
    hcorrectSeqs hardDist hhardDist 0 timeBound _ (fun _ hη =>
      let ⟨P_raw, hP⟩ := exists_cellProbeWide_of_flatPrograms s₀ p_op encode decode ν₀ hsupp₀
        opsAlphabet M_corr hη
      ⟨P_raw,
        fun ops h =>
          let ⟨hv, hl, ha⟩ := hcorrectSeqs ops h
          let ⟨_, _, hf, hx⟩ := hex_corr ops h
          (hP ops hv hl ha hf hx).1,
        fun ops h => by
          obtain ⟨hv, hl, ha⟩ := hhardDist ops h
          obtain ⟨_, _, hT, hf, hx⟩ := hex_hard ops h
          simpa only [zero_add] using (hP ops hv hl ha hf hx).2.trans (add_le_add hT le_rfl)⟩) hlb

end Cslib.DataStructure.CellProbe

/-! ### 3. `WordRAM.Randomized.StateTransitionImpl` Las Vegas simulation and lower-bound transfer -/

namespace Cslib.DataStructure.WordRAM.Randomized.StateTransitionImpl

open Cslib.DataStructure.CellProbe

universe u v

variable {B : Basis} {r_ds k_init w base : ℕ}
  {P : SubroutineCode B r_ds k_init}
  {D : StateTransitionSpec.{u, v, 0}}
  {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
  {params : Fin k_init → ℕ} {s₀ : D.State}

/-- Compile a structured `ExecStepsOfFn` derivation on `C` to `ExecFlatProgramOps` on
`P.code.program P.output`. -/
theorem ExecStepsOfFn.toExecFlatProgramOps
    (C : WordRAM.Randomized.StateTransitionImpl P D w base params s₀)
    {s : D.State} {ops : List D.Op} {ν ν_final : PMF (C.Seed × Data r_ds)} {T_ops : ℝ≥0∞}
    (hex : C.ExecStepsOfFn s ops ν ν_final T_ops)
    (hv : D.ValidHistory s ops) :
    ExecFlatProgramOps D C.Seed w base C.space (P.code.program P.output) P.input C.encode
      (fun o _ regs => C.decode o regs) s ops ν ν_final T_ops := by
  induction hex with
  | nil s ν => exact .nil s ν
  | @cons s o ops_rem ν ν_final μ_step T_step T_rest hstep _ ih =>
    obtain ⟨hvo, hv_rem⟩ := hv
    let μ_flat : C.Seed × Data r_ds → PMF (C.Seed × ℕ × Data r_ds) :=
      fun p => (μ_step p).map fun q => (q.1, q.2.regs P.output, q.2)
    have hbind_eq :
        (ν.bind fun p => (μ_flat p).map fun q => (q.1, q.2.2)) = ν.bind μ_step :=
      congrArg (ν.bind ·) (funext fun p => by
        dsimp only [μ_flat]; rw [PMF.map_comp]; exact PMF.map_id (μ_step p))
    refine .cons (μ_step := μ_flat) (T_step := T_step) (fun p hp => ?_) (hbind_eq.symm ▸ ih hv_rem)
    obtain ⟨hcdist, hq_all⟩ := hstep p hp
    have hpdist := execProgramDist_of_execCodeDist hcdist P.output
    rw [show ((μ_step p).map Prod.snd).map (fun y => (y.regs P.output, y)) =
      (μ_flat p).map Prod.snd by dsimp only [μ_flat]; rw [PMF.map_comp, PMF.map_comp]; rfl]
      at hpdist
    refine ⟨C.arguments_fit o hvo, hpdist, fun ℓ outVal y hq => ?_⟩
    obtain ⟨q₀, hq₀, hq_eq⟩ := (PMF.mem_support_map_iff _ _ _).mp hq
    obtain ⟨rfl, _, rfl⟩ := Prod.mk.inj hq_eq
    obtain ⟨hdec, hrep, hmod⟩ := hq_all q₀ hq₀
    exact ⟨C.bounded hrep, hdec, hmod⟩

/-- Initialize a `WordRAM.Randomized.StateTransitionImpl` from zeroed memory starting at `d₀`,
returning the initial coupled distribution `ν₀` and certified finite `ExecFlatProgramOps` executions
bounded by `C.initPotential + D.totalCost C.charge s₀ ops` along every valid history `ops`. -/
theorem exists_init_and_flat_steps
    (C : WordRAM.Randomized.StateTransitionImpl P D w base params s₀)
    {d₀ : Data r_ds} (hd₀ : d₀.Bounded w)
    (hfr : d₀.regs P.frontierReg = base)
    (hpar : ∀ j, d₀.regs (P.initParams j) = params j) :
    ∃ ν₀ : PMF (C.Seed × Data r_ds),
      (∀ p ∈ ν₀.support,
        p.2.Bounded w ∧ ∀ a ∉ (Block.mk base C.space).footprint, p.2.mem a = 0) ∧
      ∀ ops : List D.Op, D.ValidHistory s₀ ops →
        ∃ ν_final T_ops,
          T_ops ≤ (C.initPotential : ℝ≥0∞) + (D.totalCost C.charge s₀ ops : ℝ≥0∞) ∧
          T_ops ≠ ⊤ ∧
          ExecFlatProgramOps D C.Seed w base C.space (P.code.program P.output) P.input C.encode
            (fun o _ regs => C.decode o regs) s₀ ops ν₀ ν_final T_ops := by
  let d₀' : Data r_ds := { regs := d₀.regs, mem := fun _ => 0 }
  obtain ⟨ν₀, _, hseed₀, hsupp₀⟩ :=
    C.initFresh_exec (x := d₀') ⟨hd₀.1, fun _ => fits_zero w⟩ hfr hpar (fun _ _ => rfl)
  refine ⟨ν₀, fun p hp => ⟨C.bounded (hsupp₀ p hp).2.1, (hsupp₀ p hp).2.2.2⟩, fun ops hv => ?_⟩
  obtain ⟨ν_final, T_ops, hex, _, _, hamort⟩ :=
    C.steps_expected_amortized_ofFn ops ν₀ hv hseed₀ fun p hp => (hsupp₀ p hp).2.1
  have hpot₀ : (∑' p, ν₀ p * (C.potential p.1 p.2 : ℝ≥0∞)) ≤ (C.initPotential : ℝ≥0∞) :=
    Cslib.Probability.PMF.tsum_mul_le_of_support ν₀ fun p hp =>
      Nat.cast_le.mpr (hsupp₀ p hp).2.2.1
  have hT_le : T_ops ≤ (C.initPotential : ℝ≥0∞) + (D.totalCost C.charge s₀ ops : ℝ≥0∞) :=
    ((le_self_add.trans hamort).trans (add_le_add le_rfl hpot₀)).trans_eq (add_comm _ _)
  exact ⟨ν_final, T_ops, hT_le, ne_top_of_le_ne_top (by simp) hT_le,
    hex.toExecFlatProgramOps C hv⟩

private theorem exists_cellProbeLayout_lasVegas [∀ o, Inhabited (D.Result o)]
    (C : WordRAM.Randomized.StateTransitionImpl P D w base params s₀)
    {regCells wCell : ℕ} (L : RegLayout r_ds P.input base C.space w regCells wCell)
    {d₀ : Data r_ds} (hd₀ : d₀.Bounded w)
    (hfr : d₀.regs P.frontierReg = base)
    (hpar : ∀ j, d₀.regs (P.initParams j) = params j)
    (opsAlphabet : Finset D.Op) (M_corr : ℕ) {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ P_cp : Cslib.CellProbe.Randomized.Scheme D.Op D.Result (C.space + regCells) wCell,
      ∀ ops : List D.Op,
        D.ValidHistory s₀ ops →
        ops.length ≤ M_corr →
        (∀ o ∈ ops, o ∈ opsAlphabet) →
        (D.toObliviousSequenceSpec s₀).Contract ops ((P_cp.runSeq ops).map Prod.fst) ∧
          P_cp.expectedSeqProbes ops ≤
            (C.initPotential : ℝ≥0∞) + (D.totalCost C.charge s₀ ops : ℝ≥0∞) +
              ((L.overhead : ℝ≥0∞) + η) * (ops.length : ℝ≥0∞) := by
  obtain ⟨ν₀, hsupp₀, hsteps⟩ := C.exists_init_and_flat_steps hd₀ hfr hpar
  obtain ⟨P_cp, hP⟩ :=
    exists_cellProbeLayout_of_flatPrograms (input := P.input) s₀ L (P.code.program P.output)
      C.encode (fun o _ regs => C.decode o regs) ν₀ hsupp₀ opsAlphabet M_corr hη
  refine ⟨P_cp, fun ops hv hlen halph => ?_⟩
  obtain ⟨_, _, hT_le, hT_fin, hex⟩ := hsteps ops hv
  obtain ⟨hc, he⟩ := hP ops hv hlen halph hT_fin hex
  exact ⟨hc, he.trans (add_le_add hT_le le_rfl)⟩

/-- **Bridge 3 (Las Vegas `WordRAM.Randomized.StateTransitionImpl` → `CellProbe.Randomized.Scheme`,
standard `w`-bit layout):**
Uniformly over all admissible histories over `opsAlphabet` of length `≤ M_corr` (without
`[Fintype D.Op]`), buffered finite-horizon simulation produces a single `P_cp` on
`C.space + persistentRegCount P` cells of width `w` preserving **100% zero-error transcript
correctness** with expected probes at most
`C.initPotential + D.totalCost C.charge s₀ ops + (2 * persistentRegCount P + η) * ops.length`. -/
theorem exists_cellProbe_lasVegas [∀ o, Inhabited (D.Result o)]
    (C : WordRAM.Randomized.StateTransitionImpl P D w base params s₀)
    {d₀ : Data r_ds} (hd₀ : d₀.Bounded w)
    (hfr : d₀.regs P.frontierReg = base)
    (hpar : ∀ j, d₀.regs (P.initParams j) = params j)
    (opsAlphabet : Finset D.Op) (M_corr : ℕ) {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ P_cp :
        Cslib.CellProbe.Randomized.Scheme D.Op D.Result (C.space + persistentRegCount P) w,
      ∀ ops : List D.Op,
        D.ValidHistory s₀ ops →
        ops.length ≤ M_corr →
        (∀ o ∈ ops, o ∈ opsAlphabet) →
        (D.toObliviousSequenceSpec s₀).Contract ops ((P_cp.runSeq ops).map Prod.fst) ∧
          P_cp.expectedSeqProbes ops ≤
            (C.initPotential : ℝ≥0∞) + (D.totalCost C.charge s₀ ops : ℝ≥0∞) +
              (((2 * persistentRegCount P : ℕ) : ℝ≥0∞) + η) * (ops.length : ℝ≥0∞) := by
  rw [persistentRegCount_eq_persCount]
  simpa only [standardLayout_overhead] using
    C.exists_cellProbeLayout_lasVegas (standardLayout P.input base C.space w)
      hd₀ hfr hpar opsAlphabet M_corr hη

/-- **Wide-Cell Las Vegas Bridge (`exists_cellProbeWide_lasVegas`):**
Packs all persistent registers into `1` cell of width `wideSubroutineWidth P w` over `C.space + 1`
cells, incurring at most `2 + η` additive probes per operation regardless of `r_ds`. -/
theorem exists_cellProbeWide_lasVegas [∀ o, Inhabited (D.Result o)]
    (C : WordRAM.Randomized.StateTransitionImpl P D w base params s₀)
    {d₀ : Data r_ds} (hd₀ : d₀.Bounded w)
    (hfr : d₀.regs P.frontierReg = base)
    (hpar : ∀ j, d₀.regs (P.initParams j) = params j)
    (opsAlphabet : Finset D.Op) (M_corr : ℕ) {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ P_cp :
        Cslib.CellProbe.Randomized.Scheme D.Op D.Result (C.space + 1) (wideSubroutineWidth P w),
      ∀ ops : List D.Op,
        D.ValidHistory s₀ ops →
        ops.length ≤ M_corr →
        (∀ o ∈ ops, o ∈ opsAlphabet) →
        (D.toObliviousSequenceSpec s₀).Contract ops ((P_cp.runSeq ops).map Prod.fst) ∧
          P_cp.expectedSeqProbes ops ≤
            (C.initPotential : ℝ≥0∞) + (D.totalCost C.charge s₀ ops : ℝ≥0∞) +
              (((if persistentRegCount P = 0 then 0 else 2 : ℕ) : ℝ≥0∞) + η) *
                (ops.length : ℝ≥0∞) := by
  obtain ⟨P_cp, hP⟩ := C.exists_cellProbeLayout_lasVegas (wideLayout P.input base C.space w)
    hd₀ hfr hpar opsAlphabet M_corr hη
  refine ⟨P_cp, fun ops hv hlen halph => ?_⟩
  obtain ⟨hc, he⟩ := hP ops hv hlen halph
  rw [wideLayout_overhead, ← persistentRegCount_eq_persCount] at he
  exact ⟨hc, he⟩

end Cslib.DataStructure.WordRAM.Randomized.StateTransitionImpl

namespace Cslib.DataStructure.CellProbe

universe u v

private theorem hist_mem_univ {Op : Type*} [Fintype Op] {P : List Op → Prop} {M_corr : ℕ}
    {S : Set (List Op)} (h : ∀ ops ∈ S, P ops ∧ ops.length ≤ M_corr) :
    ∀ ops ∈ S, P ops ∧ ops.length ≤ M_corr ∧ ∀ o ∈ ops, o ∈ Finset.univ :=
  fun ops hops => ⟨(h ops hops).1, (h ops hops).2, fun _ _ => Finset.mem_univ _⟩

/-- **Contrapositive Deterministic-Cell-Probe-to-Word-RAM Lower-Bound Transfer
(`wordRAM_lower_bound_of_det_cellProbe_lower_bound`, standard `w`-bit layout):**
Any distributional probe lower bound `LB` proved against deterministic step-indexed
`IndexedScheme D.Op D.Result S_max w`s that are zero-error on `correctSeqs` (histories of length
`≤ M_corr` over `opsAlphabet`, without `[Fintype D.Op]`) transfers to the certified
potential-amortized resource budget (`initPotential + E[totalCost charge + overhead · length]`) of
every zero-error `WordRAM.Randomized.StateTransitionImpl` against `hardDist` with
`C.space + persistentRegCount P ≤ S_max` and **zero** `η` truncation loss (`0` extra cells and
`0` extra probes per operation when `∀ i, P.input i = true`). -/
theorem wordRAM_lower_bound_of_det_cellProbe_lower_bound
    {B : Basis} {r_ds k_init w base S_max : ℕ}
    {P : SubroutineCode B r_ds k_init}
    {D : StateTransitionSpec.{u, v, 0}}
    {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    {params : Fin k_init → ℕ} {s₀ : D.State}
    (C : WordRAM.Randomized.StateTransitionImpl P D w base params s₀)
    {d₀ : Data r_ds} (hd₀ : d₀.Bounded w)
    (hfr : d₀.regs P.frontierReg = base)
    (hpar : ∀ j, d₀.regs (P.initParams j) = params j)
    (hspace : C.space + persistentRegCount P ≤ S_max)
    (opsAlphabet : Finset D.Op) (M_corr : ℕ)
    (correctSeqs : Set (List D.Op))
    (hcorrectSeqs : ∀ ops ∈ correctSeqs,
      D.ValidHistory s₀ ops ∧ ops.length ≤ M_corr ∧ ∀ o ∈ ops, o ∈ opsAlphabet)
    (hardDist : PMF (List D.Op))
    (hhardDist : ∀ ops ∈ hardDist.support,
      D.ValidHistory s₀ ops ∧ ops.length ≤ M_corr ∧ ∀ o ∈ ops, o ∈ opsAlphabet)
    {LB : ℝ≥0∞}
    (hlb : ∀ D_det : IndexedScheme D.Op D.Result S_max w,
      (∀ ops ∈ correctSeqs, (D_det.runSeq ops).1 = (D.run s₀ ops).2) →
      LB ≤ ∑' ops, hardDist ops * (D_det.seqProbes ops : ℝ≥0∞)) :
    LB ≤ (C.initPotential : ℝ≥0∞) +
      ∑' ops, hardDist ops *
        ((D.totalCost C.charge s₀ ops : ℝ≥0∞) +
          ((2 * persistentRegCount P : ℕ) : ℝ≥0∞) * (ops.length : ℝ≥0∞)) :=
  lower_bound_of_exists_cellProbeLayout s₀ hspace opsAlphabet M_corr correctSeqs hcorrectSeqs
    hardDist hhardDist _ _ _ (fun _ hη =>
      let ⟨P_raw, hP⟩ := C.exists_cellProbe_lasVegas hd₀ hfr hpar opsAlphabet M_corr hη
      ⟨P_raw,
        fun ops h => (hP ops (hcorrectSeqs ops h).1 (hcorrectSeqs ops h).2.1
          (hcorrectSeqs ops h).2.2).1,
        fun ops h => (hP ops (hhardDist ops h).1 (hhardDist ops h).2.1
          (hhardDist ops h).2.2).2⟩) hlb

/-- `[Finite D.Op]` convenience specialization of
`wordRAM_lower_bound_of_det_cellProbe_lower_bound`, instantiating `opsAlphabet := Finset.univ`. -/
theorem wordRAM_lower_bound_of_det_cellProbe_of_fintype
    {B : Basis} {r_ds k_init w base S_max : ℕ}
    {P : SubroutineCode B r_ds k_init}
    {D : StateTransitionSpec.{u, v, 0}} [Finite D.Op]
    {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    {params : Fin k_init → ℕ} {s₀ : D.State}
    (C : WordRAM.Randomized.StateTransitionImpl P D w base params s₀)
    {d₀ : Data r_ds} (hd₀ : d₀.Bounded w)
    (hfr : d₀.regs P.frontierReg = base)
    (hpar : ∀ j, d₀.regs (P.initParams j) = params j)
    (hspace : C.space + persistentRegCount P ≤ S_max)
    (M_corr : ℕ) (correctSeqs : Set (List D.Op))
    (hcorrectSeqs : ∀ ops ∈ correctSeqs, D.ValidHistory s₀ ops ∧ ops.length ≤ M_corr)
    (hardDist : PMF (List D.Op))
    (hhardDist : ∀ ops ∈ hardDist.support, D.ValidHistory s₀ ops ∧ ops.length ≤ M_corr)
    {LB : ℝ≥0∞}
    (hlb : ∀ D_det : IndexedScheme D.Op D.Result S_max w,
      (∀ ops ∈ correctSeqs, (D_det.runSeq ops).1 = (D.run s₀ ops).2) →
      LB ≤ ∑' ops, hardDist ops * (D_det.seqProbes ops : ℝ≥0∞)) :
    LB ≤ (C.initPotential : ℝ≥0∞) +
      ∑' ops, hardDist ops *
        ((D.totalCost C.charge s₀ ops : ℝ≥0∞) +
          ((2 * persistentRegCount P : ℕ) : ℝ≥0∞) * (ops.length : ℝ≥0∞)) := by
  cases nonempty_fintype D.Op
  exact wordRAM_lower_bound_of_det_cellProbe_lower_bound C hd₀ hfr hpar hspace Finset.univ M_corr
    correctSeqs (hist_mem_univ hcorrectSeqs) hardDist (hist_mem_univ hhardDist) hlb

/-- **Wide-Cell Contrapositive Word-RAM Lower-Bound Transfer
(`wordRAM_lower_bound_of_det_cellProbe_wide`):**
Transfers any deterministic step-indexed cell-probe lower bound at cell width
`wideSubroutineWidth P w := max (persistentRegCount P) 1 * w` and space `S_max ≥ C.space + 1` to
the certified potential-amortized resource budget of any zero-error `r_ds`-register
`WordRAM.Randomized.StateTransitionImpl` against `hardDist` with **at most `2` additive probes per
operation** and **zero** `η` truncation loss. -/
theorem wordRAM_lower_bound_of_det_cellProbe_wide
    {B : Basis} {r_ds k_init w base S_max : ℕ}
    {P : SubroutineCode B r_ds k_init}
    {D : StateTransitionSpec.{u, v, 0}}
    {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    {params : Fin k_init → ℕ} {s₀ : D.State}
    (C : WordRAM.Randomized.StateTransitionImpl P D w base params s₀)
    {d₀ : Data r_ds} (hd₀ : d₀.Bounded w)
    (hfr : d₀.regs P.frontierReg = base)
    (hpar : ∀ j, d₀.regs (P.initParams j) = params j)
    (hspace : C.space + 1 ≤ S_max)
    (opsAlphabet : Finset D.Op) (M_corr : ℕ)
    (correctSeqs : Set (List D.Op))
    (hcorrectSeqs : ∀ ops ∈ correctSeqs,
      D.ValidHistory s₀ ops ∧ ops.length ≤ M_corr ∧ ∀ o ∈ ops, o ∈ opsAlphabet)
    (hardDist : PMF (List D.Op))
    (hhardDist : ∀ ops ∈ hardDist.support,
      D.ValidHistory s₀ ops ∧ ops.length ≤ M_corr ∧ ∀ o ∈ ops, o ∈ opsAlphabet)
    {LB : ℝ≥0∞}
    (hlb : ∀ D_det : IndexedScheme D.Op D.Result S_max (wideSubroutineWidth P w),
      (∀ ops ∈ correctSeqs, (D_det.runSeq ops).1 = (D.run s₀ ops).2) →
      LB ≤ ∑' ops, hardDist ops * (D_det.seqProbes ops : ℝ≥0∞)) :
    LB ≤ (C.initPotential : ℝ≥0∞) +
      ∑' ops, hardDist ops *
        ((D.totalCost C.charge s₀ ops : ℝ≥0∞) + (2 : ℝ≥0∞) * (ops.length : ℝ≥0∞)) :=
  lower_bound_of_exists_cellProbeLayout s₀ hspace opsAlphabet M_corr correctSeqs hcorrectSeqs
    hardDist hhardDist _ _ (2 : ℝ≥0∞) (fun _ hη =>
      let ⟨P_raw, hP⟩ := C.exists_cellProbeWide_lasVegas hd₀ hfr hpar opsAlphabet M_corr hη
      ⟨P_raw,
        fun ops h => (hP ops (hcorrectSeqs ops h).1 (hcorrectSeqs ops h).2.1
          (hcorrectSeqs ops h).2.2).1,
        fun ops h => (hP ops (hhardDist ops h).1 (hhardDist ops h).2.1
          (hhardDist ops h).2.2).2.trans (add_le_add le_rfl (mul_le_mul'
            (add_le_add (by split_ifs <;> norm_num) le_rfl) le_rfl))⟩) hlb

/-- `[Finite D.Op]` convenience specialization of `wordRAM_lower_bound_of_det_cellProbe_wide`. -/
theorem wordRAM_lower_bound_of_det_cellProbe_wide_of_fintype
    {B : Basis} {r_ds k_init w base S_max : ℕ}
    {P : SubroutineCode B r_ds k_init}
    {D : StateTransitionSpec.{u, v, 0}} [Finite D.Op]
    {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    {params : Fin k_init → ℕ} {s₀ : D.State}
    (C : WordRAM.Randomized.StateTransitionImpl P D w base params s₀)
    {d₀ : Data r_ds} (hd₀ : d₀.Bounded w)
    (hfr : d₀.regs P.frontierReg = base)
    (hpar : ∀ j, d₀.regs (P.initParams j) = params j)
    (hspace : C.space + 1 ≤ S_max)
    (M_corr : ℕ) (correctSeqs : Set (List D.Op))
    (hcorrectSeqs : ∀ ops ∈ correctSeqs, D.ValidHistory s₀ ops ∧ ops.length ≤ M_corr)
    (hardDist : PMF (List D.Op))
    (hhardDist : ∀ ops ∈ hardDist.support, D.ValidHistory s₀ ops ∧ ops.length ≤ M_corr)
    {LB : ℝ≥0∞}
    (hlb : ∀ D_det : IndexedScheme D.Op D.Result S_max (wideSubroutineWidth P w),
      (∀ ops ∈ correctSeqs, (D_det.runSeq ops).1 = (D.run s₀ ops).2) →
      LB ≤ ∑' ops, hardDist ops * (D_det.seqProbes ops : ℝ≥0∞)) :
    LB ≤ (C.initPotential : ℝ≥0∞) +
      ∑' ops, hardDist ops *
        ((D.totalCost C.charge s₀ ops : ℝ≥0∞) + (2 : ℝ≥0∞) * (ops.length : ℝ≥0∞)) := by
  cases nonempty_fintype D.Op
  exact wordRAM_lower_bound_of_det_cellProbe_wide C hd₀ hfr hpar hspace Finset.univ M_corr
    correctSeqs (hist_mem_univ hcorrectSeqs) hardDist (hist_mem_univ hhardDist) hlb

end Cslib.DataStructure.CellProbe

/-! ### 4. `WordRAM.Randomized.ObliviousSequenceImpl` simulation and lower-bound transfer -/

namespace Cslib.DataStructure.WordRAM.Randomized

open Cslib.DataStructure.CellProbe

universe u z

/-- Finite-tree `ExecRand` step witness for an `ObliviousSequenceImpl`: strengthens `ExecSteps` by
witnessing a finite `ProbComp (Data r_ds × ℕ)` computation `mc t` (`ExecRand`) on each step rather
than an unbounded `ExecCodeDist` loop, enabling exact zero-slack `RandProbeTree` simulation on
arbitrary (including Monte Carlo) `ObliviousSequenceSpec`s. -/
inductive ExecStepsRand {B : Basis} {r_ds k_init : ℕ}
    (P : SubroutineCode B r_ds k_init)
    (S : DataStructure.ObliviousSequenceSpec.{u, 0})
    (Latent : Type z) (w base space : ℕ)
    (encode : S.Op → Fin r_ds → ℕ)
    (decode : (o : S.Op) → (Fin r_ds → ℕ) → Option (S.Result o)) :
    List S.Op → PMF (SeqOutcome Latent S.Result r_ds) →
      PMF (SeqOutcome Latent S.Result r_ds) → ℝ≥0∞ → Prop where
  | nil (ν : PMF (SeqOutcome Latent S.Result r_ds)) :
      ExecStepsRand P S Latent w base space encode decode [] ν ν 0
  | cons {o : S.Op} {ops : List S.Op}
      {ν ν_final : PMF (SeqOutcome Latent S.Result r_ds)}
      {mc : SeqOutcome Latent S.Result r_ds → ProbComp (Data r_ds × ℕ)}
      {μ_step : SeqOutcome Latent S.Result r_ds → PMF (StepOutcome Latent (S.Result o) r_ds)}
      {T_rest : ℝ≥0∞} :
      (∀ t ∈ ν.support,
        t.data.Bounded w ∧
        (∀ i, P.input i = true → Fits w (encode o i)) ∧
        ExecRand w P.code (P.prepare encode o t.data) (mc t) ∧
        (mc t).eval.map Prod.fst = (μ_step t).map StepOutcome.data ∧
        ∀ q ∈ (μ_step t).support,
          q.data.Bounded w ∧
          decode o q.data.regs = some q.result ∧
          Modifies (Block.mk base space).footprint t.data.mem q.data.mem) →
      ExecStepsRand P S Latent w base space encode decode ops
        (ν.bind fun t => (μ_step t).map (t.appendStep o)) ν_final T_rest →
      ExecStepsRand P S Latent w base space encode decode (o :: ops) ν ν_final
        ((∑' t, ν t * ProbComp.expect (mc t) (fun z => (z.2 : ℝ≥0∞))) + T_rest)

/-- Every finite-tree `ExecStepsRand` trace embeds directly into `ExecSteps` via
`ExecCodeDist.of_execRand`. -/
theorem ExecStepsRand.toExecSteps {B : Basis} {r_ds k_init : ℕ}
    {P : SubroutineCode B r_ds k_init}
    {S : DataStructure.ObliviousSequenceSpec.{u, 0}}
    {Latent : Type z} {w base space : ℕ}
    {encode : S.Op → Fin r_ds → ℕ}
    {decode : (o : S.Op) → (Fin r_ds → ℕ) → Option (S.Result o)}
    {ops : List S.Op} {ν ν_final : PMF (SeqOutcome Latent S.Result r_ds)} {T_ops : ℝ≥0∞}
    (h : ExecStepsRand P S Latent w base space encode decode ops ν ν_final T_ops) :
    ExecSteps P S Latent w base space encode decode ops ν ν_final T_ops := by
  induction h with
  | nil ν => exact .nil ν
  | @cons o ops ν ν_final mc μ_step T_rest hstep _ ih =>
    refine .cons (fun t ht => ?_) ih
    obtain ⟨hbdd, harg, hexr, hmap, hq⟩ := hstep t ht
    have hprep_bdd : (P.prepare encode o t.data).Bounded w :=
      P.prepare_bounded encode hbdd harg
    have hdist : ExecCodeDist w P.code (P.prepare encode o t.data)
        ((μ_step t).map StepOutcome.data) (ProbComp.expect (mc t) fun z => (z.2 : ℝ≥0∞)) := by
      have hc := ExecCodeDist.of_execRand hexr
      rwa [ProbComp.eval_map, hmap] at hc
    exact ⟨hbdd, harg, hprep_bdd, hdist, hq⟩

/-- Predicate asserting that every admissible sequence on `C : ObliviousSequenceImpl` executes via
finite `ExecRand` computation trees (`ExecStepsRand`). -/
@[expose] def ObliviousSequenceImpl.HasFiniteExecRand {B : Basis} {r_ds k_init w base : ℕ}
    {P : SubroutineCode B r_ds k_init}
    {S : DataStructure.ObliviousSequenceSpec.{u, 0}}
    {params : Fin k_init → ℕ}
    (C : ObliviousSequenceImpl.{u, 0, z} P S w base params) : Prop :=
  ∀ (ops : List S.Op) (ν₀ : PMF (LatentState C.Latent r_ds)),
    S.ValidOpSeq ops → C.initInv ν₀ →
    ∃ (ν_final : PMF (SeqOutcome C.Latent S.Result r_ds)) (T_ops : ℝ≥0∞),
      ExecStepsRand P S C.Latent w base C.space C.encode C.decode ops
        (ν₀.map SeqOutcome.ofLatentState) ν_final T_ops ∧
      S.Contract ops (ν_final.map SeqOutcome.transcript) ∧
      T_ops ≤ (C.initPotential : ℝ≥0∞) + ((ops.map C.charge).sum : ℝ≥0∞)

private theorem ObliviousSequenceImpl.initFresh_seqOutcome
    {B : Basis} {r_ds k_init w base : ℕ}
    {P : SubroutineCode B r_ds k_init}
    {S : DataStructure.ObliviousSequenceSpec.{u, 0}}
    {params : Fin k_init → ℕ}
    (C : ObliviousSequenceImpl.{u, 0, z} P S w base params)
    {d₀ : Data r_ds} (hd₀ : d₀.Bounded w)
    (hfr : d₀.regs P.frontierReg = base)
    (hpar : ∀ j, d₀.regs (P.initParams j) = params j) :
    ∃ ν₀ : PMF (LatentState C.Latent r_ds),
      C.initInv ν₀ ∧
      ∀ t ∈ (ν₀.map (SeqOutcome.ofLatentState (Result := S.Result))).support,
        t.data.Bounded w ∧ ∀ a ∉ (Block.mk base C.space).footprint, t.data.mem a = 0 := by
  let d₀' : Data r_ds := { regs := d₀.regs, mem := fun _ => 0 }
  obtain ⟨ν₀, _, hinv₀, hsupp₀⟩ :=
    C.initFresh_exec (x := d₀') ⟨hd₀.1, fun _ => fits_zero w⟩ hfr hpar (fun _ _ => rfl)
  refine ⟨ν₀, hinv₀, fun t ht => ?_⟩
  obtain ⟨z₀, hz₀, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp ht
  exact ⟨(hsupp₀ z₀ hz₀).1, fun a ha => (hsupp₀ z₀ hz₀).2.2 a ha⟩

private theorem simExecStepsRand_induction {B : Basis} {r_ds k_init regCells wCell w base space : ℕ}
    {P : SubroutineCode B r_ds k_init}
    {S : DataStructure.ObliviousSequenceSpec.{u, 0}} [∀ o, Inhabited (S.Result o)]
    {Latent : Type z}
    {encode : S.Op → Fin r_ds → ℕ}
    {decode : (o : S.Op) → (Fin r_ds → ℕ) → Option (S.Result o)}
    (L : RegLayout r_ds P.input base space w regCells wCell)
    (initMem : PMF (Mem (space + regCells) wCell))
    {ops : List S.Op} {ν ν_final : PMF (SeqOutcome Latent S.Result r_ds)} {T_ops : ℝ≥0∞}
    (hex : ExecStepsRand P S Latent w base space encode decode ops ν ν_final T_ops)
    (hsupp : ∀ t ∈ ν.support,
      t.data.Bounded w ∧ ∀ a ∉ (Block.mk base space).footprint, t.data.mem a = 0) :
    let P_cp : Cslib.CellProbe.Randomized.Scheme S.Op S.Result (space + regCells) wCell :=
      { init := initMem
        step := fun o =>
          simProgRand (w := w) L (P.code.program P.output) (encode o)
            (fun _ regs => decode o regs) default (autoRandFuel L P.code (encode o)) }
    (ν.bind fun t =>
        ((P_cp.runFrom (L.pack t.data) ops).map Prod.fst).map (fun tm => t.transcript ++ tm.1)) =
      ν_final.map SeqOutcome.transcript ∧
    (∑' t, ν t * P_cp.expectedProbesFrom (L.pack t.data) ops) ≤
      T_ops + (L.overhead : ℝ≥0∞) * (ops.length : ℝ≥0∞) := by
  intro P_cp
  induction hex with
  | nil ν =>
    refine ⟨?_, by simp [Cslib.CellProbe.Randomized.Scheme.expectedProbesFrom]⟩
    simp only [Cslib.CellProbe.Randomized.Scheme.runFrom, PMF.pure_map, List.append_nil]
    exact PMF.bind_pure_comp SeqOutcome.transcript ν
  | @cons o ops_rem ν ν_final mc μ_step T_rest hstep _ ih =>
    have hsupp₁ := bounded_zeroOutside_bind_map ν μ_step (fun t q => t.appendStep o q)
      SeqOutcome.data StepOutcome.data (fun _ _ => rfl) hsupp fun t ht q hq =>
        ⟨(hstep t ht).2.2.2.2 q hq |>.1, (hstep t ht).2.2.2.2 q hq |>.2.2⟩
    obtain ⟨hlaw_rem, hexp_rem⟩ := ih hsupp₁
    have hstep_law : ∀ t ∈ ν.support,
        ((P_cp.step o).run (L.pack t.data)).map Prod.fst =
          (μ_step t).map (fun q => (q.result, L.pack q.data)) ∧
        (P_cp.step o).expectedProbes (L.pack t.data) ≤
          ProbComp.expect (mc t) (fun z => (z.2 : ℝ≥0∞)) + (L.overhead : ℝ≥0∞) := by
      intro t ht
      obtain ⟨_, harg, hexec_t, hmc_eq, hq_all⟩ := hstep t ht
      change ExecRand w P.code (prepareFlatRegs P.input encode o t.data) (mc t) at hexec_t
      rw [← unpack_pack_eq_prepareFlatRegs L encode o (hsupp t ht).1 (hsupp t ht).2] at hexec_t
      obtain ⟨hlaw_sim, hexp_sim⟩ :=
        simExecRandLayout L P.code P.output (encode o) (decode o) (default : S.Result o)
          (L.validMem_pack t.data) harg hexec_t
      refine ⟨?_, hexp_sim⟩
      rw [hlaw_sim, show (mc t).eval.map (fun z => ((decode o z.1.regs).getD default, L.pack z.1)) =
        ((mc t).eval.map Prod.fst).map (fun y => ((decode o y.regs).getD default, L.pack y)) by
          rw [PMF.map_comp]; rfl,
        hmc_eq, PMF.map_comp]
      exact Cslib.Probability.PMF.map_congr_on_support (μ_step t) _ _ fun q hq => by
        simp [(hq_all q hq).2.1]
    refine ⟨?_, ?_⟩
    · rw [← hlaw_rem, PMF.bind_bind]
      refine Cslib.Probability.PMF.bind_congr_on_support ν _ _ fun t ht => ?_
      rw [P_cp.runFrom_cons_fst, PMF.map_bind, (hstep_law t ht).1, PMF.bind_map, PMF.bind_map]
      exact congrArg ((μ_step t).bind ·) (funext fun q => by
        simp [Function.comp_def, SeqOutcome.appendStep, PMF.map_comp])
    · refine tsum_expectedProbesFrom_cons_le P_cp ν μ_step (fun t q => t.appendStep o q)
        (fun t => L.pack t.data) (fun t => ProbComp.expect (mc t) (fun z => (z.2 : ℝ≥0∞)))
        (L.overhead : ℝ≥0∞) T_rest o ops_rem hexp_rem fun t ht => ?_
      obtain ⟨hlaw_t, hexp_t⟩ := hstep_law t ht
      rw [P_cp.expectedProbesFrom_cons, hlaw_t, Probability.PMF.tsum_map_mul]
      exact add_le_add hexp_t le_rfl

/-- **Bridge 2 (`ObliviousSequenceImpl.exists_cellProbe_of_execRand`, exact finite-tree
simulation):**
When `C : ObliviousSequenceImpl` satisfies `C.HasFiniteExecRand`, `C` induces a
`CellProbe.Randomized.ObliviousSequenceImpl` on `C.space + persistentRegCount P` cells of width `w`
reproducing the **exact** transcript distribution (`S.Contract ops` holds on arbitrary — including
Monte Carlo — `ObliviousSequenceSpec`s with `0` error distortion and `0` `η`-loss) and per-operation
probe charge `C.charge o + 2 * persistentRegCount P`. -/
theorem ObliviousSequenceImpl.exists_cellProbe_of_execRand
    {B : Basis} {r_ds k_init w base : ℕ}
    {P : SubroutineCode B r_ds k_init}
    {S : DataStructure.ObliviousSequenceSpec.{u, 0}} [∀ o, Inhabited (S.Result o)]
    {params : Fin k_init → ℕ}
    (C : ObliviousSequenceImpl.{u, 0, z} P S w base params)
    {d₀ : Data r_ds} (hd₀ : d₀.Bounded w)
    (hfr : d₀.regs P.frontierReg = base)
    (hpar : ∀ j, d₀.regs (P.initParams j) = params j)
    (hfin : C.HasFiniteExecRand) :
    ∃ P_cp :
        Cslib.CellProbe.Randomized.Scheme S.Op S.Result (C.space + persistentRegCount P) w,
      ∃ C_cp : Cslib.DataStructure.CellProbe.Randomized.ObliviousSequenceImpl S P_cp,
        C_cp.initPotential = C.initPotential ∧
        (∀ o, C_cp.charge o = C.charge o + 2 * persistentRegCount P) := by
  rw [persistentRegCount_eq_persCount]
  let L := standardLayout P.input base C.space w
  obtain ⟨ν₀, hinv₀, hsupp_seq⟩ := C.initFresh_seqOutcome hd₀ hfr hpar
  set ν₀_seq := ν₀.map (SeqOutcome.ofLatentState (Result := S.Result))
  let P_cp : Cslib.CellProbe.Randomized.Scheme S.Op S.Result (C.space + persCount P.input) w :=
    { init := ν₀_seq.map fun t => L.pack t.data
      step := fun o =>
        simProgRand (w := w) L (P.code.program P.output) (C.encode o)
          (fun _ regs => C.decode o regs) default (autoRandFuel L P.code (C.encode o)) }
  refine ⟨P_cp, ⟨{
    initPotential := C.initPotential
    charge := fun o => C.charge o + 2 * persCount P.input
    contract_runSeq := ?_
    expectedSeqProbes_le := ?_
  }, rfl, fun _ => rfl⟩⟩
  · intro ops hv
    obtain ⟨ν_final, T_ops, hex, hcontract, _⟩ := hfin ops ν₀ hv hinv₀
    obtain ⟨hlaw, _⟩ :=
      simExecStepsRand_induction L (ν₀_seq.map fun t => L.pack t.data) hex hsupp_seq
    have hrun_eq : (P_cp.runSeq ops).map Prod.fst = ν_final.map SeqOutcome.transcript := by
      rw [← hlaw, Cslib.CellProbe.Randomized.Scheme.runSeq]
      dsimp only [P_cp]
      rw [PMF.map_bind, PMF.bind_map]
      refine Cslib.Probability.PMF.bind_congr_on_support ν₀_seq _ _ fun t ht => ?_
      obtain ⟨_, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp ht
      simp [SeqOutcome.ofLatentState, PMF.map_comp, Function.comp_def]
    exact hrun_eq ▸ hcontract
  · intro ops hv
    obtain ⟨ν_final, T_ops, hex, _, hcost⟩ := hfin ops ν₀ hv hinv₀
    obtain ⟨_, hexp⟩ :=
      simExecStepsRand_induction L (ν₀_seq.map fun t => L.pack t.data) hex hsupp_seq
    rw [Cslib.CellProbe.Randomized.Scheme.expectedSeqProbes_eq_init_tsum]
    dsimp only [P_cp]
    rw [Probability.PMF.tsum_map_mul]
    rw [show (L.overhead : ℝ≥0∞) = ((2 * persCount P.input : ℕ) : ℝ≥0∞) from
      congrArg Nat.cast (standardLayout_overhead P.input base C.space w)] at hexp
    rw [show ((ops.map fun o => C.charge o + 2 * persCount P.input).sum : ℕ) =
        (ops.map C.charge).sum + 2 * persCount P.input * ops.length by
          simp [List.sum_map_add, mul_comm],
      Nat.cast_add, Nat.cast_mul]
    exact hexp.trans ((add_le_add hcost le_rfl).trans_eq (by ac_rfl))

private theorem simExecStepsLasVegas_induction
    {B : Basis} {r_ds k_init regCells wCell w base space : ℕ}
    {P : SubroutineCode B r_ds k_init}
    {S : DataStructure.ObliviousSequenceSpec.{u, 0}} [∀ o, Inhabited (S.Result o)]
    {Latent : Type z}
    {encode : S.Op → Fin r_ds → ℕ}
    {decode : (o : S.Op) → (Fin r_ds → ℕ) → Option (S.Result o)}
    (L : RegLayout r_ds P.input base space w regCells wCell)
    (initMem : PMF (Mem (space + regCells) wCell))
    (opsAlphabet : Finset S.Op) (M_corr K : ℕ) (η : ℝ≥0∞)
    (hK_tail : ∀ o ∈ opsAlphabet, ∀ m : Mem (space + regCells) wCell,
      (∃ μ_p : PMF (ℕ × Data r_ds), ∃ T_p : ℝ≥0∞, T_p ≠ ⊤ ∧
        ExecProgramDist w (P.code.program P.output) (L.unpack (encode o) m) μ_p (T_p + 1)) →
      (evalRand w (P.code.program P.output) K ⟨0, L.unpack (encode o) m⟩).toOuterMeasure
          (RandCfg.runningSet r_ds) *
        ((((2 * space + regCells) + M_corr * (2 * space + regCells + L.overhead) : ℕ) : ℝ≥0∞) +
          (M_corr : ℝ≥0∞) * (K : ℝ≥0∞)) ≤ η)
    {ops : List S.Op} {ν ν_final : PMF (SeqOutcome Latent S.Result r_ds)} {T_ops : ℝ≥0∞}
    (hex : ExecSteps P S Latent w base space encode decode ops ν ν_final T_ops)
    (hlen : ops.length ≤ M_corr)
    (halph : ∀ o ∈ ops, o ∈ opsAlphabet)
    (hT_fin : T_ops ≠ ⊤)
    (hsupp : ∀ t ∈ ν.support,
      t.data.Bounded w ∧ ∀ a ∉ (Block.mk base space).footprint, t.data.mem a = 0) :
    let P_cp : Cslib.CellProbe.Randomized.Scheme S.Op S.Result (space + regCells) wCell :=
      { init := initMem
        step := fun o =>
          simProgRand (w := w) L (P.code.program P.output) (encode o)
            (fun _ regs => decode o regs) default K }
    (∀ t ∈ ν.support, ∀ tm ∈ ((P_cp.runFrom (L.pack t.data) ops).map Prod.fst).support,
      t.transcript ++ tm.1 ∈ (ν_final.map SeqOutcome.transcript).support) ∧
    (∑' t, ν t * P_cp.expectedProbesFrom (L.pack t.data) ops) ≤
      T_ops + ((L.overhead : ℝ≥0∞) + η) * (ops.length : ℝ≥0∞) := by
  intro P_cp
  set p_op := P.code.program P.output
  have hW_step : ∀ o' m, (P_cp.step o').expectedProbes m ≤
      ((K + 2 * space + regCells + L.overhead : ℕ) : ℝ≥0∞) := fun o' m =>
    simProgRand_expectedProbes_le_worstCase L p_op (encode o')
      (fun _ regs => decode o' regs) default K m
  induction hex with
  | nil ν =>
    refine ⟨fun t ht tm htm => ?_, by simp [Cslib.CellProbe.Randomized.Scheme.expectedProbesFrom]⟩
    simp only [Cslib.CellProbe.Randomized.Scheme.runFrom, PMF.pure_map, PMF.support_pure,
      Set.mem_singleton_iff] at htm
    rw [htm, List.append_nil]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨t, ht, rfl⟩
  | @cons o ops_rem ν ν_final μ_step T_step T_rest hstep _ ih =>
    have hsum_fin : (∑' t, ν t * T_step t) ≠ ⊤ := ne_top_of_le_ne_top hT_fin le_self_add
    have hsupp₁ := bounded_zeroOutside_bind_map ν μ_step (fun t q => t.appendStep o q)
      SeqOutcome.data StepOutcome.data (fun _ _ => rfl) hsupp fun t ht q hq =>
        ⟨(hstep t ht).2.2.2.2 q hq |>.1, (hstep t ht).2.2.2.2 q hq |>.2.2⟩
    obtain ⟨hcorr_rem, hexp_rem⟩ := ih (Nat.le_of_succ_le hlen)
      (fun o' ho' => halph o' (List.mem_cons_of_mem o ho'))
      (ne_top_of_le_ne_top hT_fin le_add_self) hsupp₁
    have hstep_cp := fun t (ht : t ∈ ν.support) =>
      let hpdist : ExecProgramDist w p_op (prepareFlatRegs P.input encode o t.data)
          ((μ_step t).map fun q => (q.data.regs P.output, q.data)) (T_step t + 1) := by
        have hp := execProgramDist_of_execCodeDist (hstep t ht).2.2.2.1 P.output
        rwa [PMF.map_comp] at hp
      lasVegas_cons_step L P_cp p_op encode (fun _ regs => decode o regs) (default : S.Result o)
        K M_corr η rfl hW_step (Nat.le_of_succ_le hlen) (hsupp t ht).1 (hsupp t ht).2
        (hstep t ht).2.1 (ne_top_of_mem_support_of_tsum_ne_top hsum_fin ht)
        hpdist (hK_tail o (halph o List.mem_cons_self))
    refine ⟨?_, ?_⟩
    · intro t ht tm htm
      obtain ⟨vy, hvy, tm_rem, htm_rem, rfl⟩ := (hstep_cp t ht).1 tm htm
      obtain ⟨q, hq, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hvy
      simpa only [SeqOutcome.appendStep, List.append_assoc, List.singleton_append,
        ((hstep t ht).2.2.2.2 q hq).2.1, Option.getD_some] using
        hcorr_rem (t.appendStep o q) (mem_support_bind_map ht hq) tm_rem htm_rem
    · refine tsum_expectedProbesFrom_cons_le P_cp ν μ_step (fun t q => t.appendStep o q)
        (fun t => L.pack t.data) T_step ((L.overhead : ℝ≥0∞) + η) T_rest o ops_rem hexp_rem
        fun t ht => ?_
      have h2 := (hstep_cp t ht).2
      rwa [Probability.PMF.tsum_map_mul (μ_step t) (fun q => (q.data.regs P.output, q.data))] at h2

end Cslib.DataStructure.WordRAM.Randomized

namespace Cslib.DataStructure.WordRAM.Randomized.ObliviousSequenceImpl

open Cslib.DataStructure.CellProbe

universe u v z

/-- Layout-parametric buffered Las Vegas simulation of any `ObliviousSequenceImpl` over
`D.toObliviousSequenceSpec s₀` (even for nondeterministic relational `D`, without `[D.HasStepFn f]`
or `[Fintype D.Op]`). -/
theorem exists_cellProbeLayout_lasVegas
    {B : Basis} {r_ds k_init regCells wCell w base : ℕ}
    {P : SubroutineCode B r_ds k_init}
    {D : StateTransitionSpec.{u, v, 0}} [∀ o, Inhabited (D.Result o)]
    {params : Fin k_init → ℕ} {s₀ : D.State}
    (C : ObliviousSequenceImpl.{v, 0, z} P (D.toObliviousSequenceSpec s₀) w base params)
    (L : RegLayout r_ds P.input base C.space w regCells wCell)
    {d₀ : Data r_ds} (hd₀ : d₀.Bounded w)
    (hfr : d₀.regs P.frontierReg = base)
    (hpar : ∀ j, d₀.regs (P.initParams j) = params j)
    (opsAlphabet : Finset D.Op) (M_corr : ℕ) {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ P_cp : Cslib.CellProbe.Randomized.Scheme D.Op D.Result (C.space + regCells) wCell,
      ∀ ops : List D.Op,
        D.ValidOpSeq s₀ ops →
        ops.length ≤ M_corr →
        (∀ o ∈ ops, o ∈ opsAlphabet) →
        (D.toObliviousSequenceSpec s₀).Contract ops ((P_cp.runSeq ops).map Prod.fst) ∧
          P_cp.expectedSeqProbes ops ≤
            (C.initPotential : ℝ≥0∞) + ((ops.map C.charge).sum : ℝ≥0∞) +
              ((L.overhead : ℝ≥0∞) + η) * (ops.length : ℝ≥0∞) := by
  obtain ⟨ν₀, hinv₀, hsupp_seq⟩ := C.initFresh_seqOutcome hd₀ hfr hpar
  let ν₀_seq := ν₀.map (SeqOutcome.ofLatentState (Result := D.Result))
  set p_op := P.code.program P.output
  obtain ⟨K, hK_tail⟩ := exists_uniform_cutoff_singleProg L opsAlphabet p_op C.encode M_corr hη
  let P_cp : Cslib.CellProbe.Randomized.Scheme D.Op D.Result (C.space + regCells) wCell :=
    { init := ν₀_seq.map fun t => L.pack t.data
      step := fun o =>
        simProgRand (w := w) L p_op (C.encode o) (fun _ regs => C.decode o regs) default K }
  refine ⟨P_cp, fun ops hv hlen halph => ?_⟩
  obtain ⟨ν_final, T_ops, hex, hcontract, hcost⟩ := C.steps_exec ops ν₀ hv hinv₀
  obtain ⟨hcorr, hexp⟩ :=
    simExecStepsLasVegas_induction L (ν₀_seq.map fun t => L.pack t.data) opsAlphabet M_corr K η
      hK_tail hex hlen halph
      (ne_top_of_le_ne_top
        (ENNReal.add_ne_top.mpr ⟨ENNReal.natCast_ne_top _, ENNReal.natCast_ne_top _⟩) hcost)
      hsupp_seq
  refine ⟨fun tr htr => ?_, ?_⟩
  · obtain ⟨t, ht, m_fin, htm⟩ := mem_support_map_fst_runSeq_of_map P_cp rfl htr
    obtain ⟨_, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp ht
    exact hcontract tr (by simpa [SeqOutcome.ofLatentState] using hcorr _ ht (tr, m_fin) htm)
  · rw [Cslib.CellProbe.Randomized.Scheme.expectedSeqProbes_eq_init_tsum,
      Probability.PMF.tsum_map_mul]
    exact hexp.trans (add_le_add hcost le_rfl)

/-- Standard `w`-bit Las Vegas simulation of any zero-error `ObliviousSequenceImpl` over
`D.toObliviousSequenceSpec s₀`. -/
theorem exists_cellProbe_lasVegas
    {B : Basis} {r_ds k_init w base : ℕ}
    {P : SubroutineCode B r_ds k_init}
    {D : StateTransitionSpec.{u, v, 0}} [∀ o, Inhabited (D.Result o)]
    {params : Fin k_init → ℕ} {s₀ : D.State}
    (C : ObliviousSequenceImpl.{v, 0, z} P (D.toObliviousSequenceSpec s₀) w base params)
    {d₀ : Data r_ds} (hd₀ : d₀.Bounded w)
    (hfr : d₀.regs P.frontierReg = base)
    (hpar : ∀ j, d₀.regs (P.initParams j) = params j)
    (opsAlphabet : Finset D.Op) (M_corr : ℕ) {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ P_cp :
        Cslib.CellProbe.Randomized.Scheme D.Op D.Result (C.space + persistentRegCount P) w,
      ∀ ops : List D.Op,
        D.ValidOpSeq s₀ ops →
        ops.length ≤ M_corr →
        (∀ o ∈ ops, o ∈ opsAlphabet) →
        (D.toObliviousSequenceSpec s₀).Contract ops ((P_cp.runSeq ops).map Prod.fst) ∧
          P_cp.expectedSeqProbes ops ≤
            (C.initPotential : ℝ≥0∞) + ((ops.map C.charge).sum : ℝ≥0∞) +
              (((2 * persistentRegCount P : ℕ) : ℝ≥0∞) + η) * (ops.length : ℝ≥0∞) := by
  rw [persistentRegCount_eq_persCount]
  simpa only [standardLayout_overhead] using
    C.exists_cellProbeLayout_lasVegas (standardLayout P.input base C.space w)
      hd₀ hfr hpar opsAlphabet M_corr hη

end Cslib.DataStructure.WordRAM.Randomized.ObliviousSequenceImpl

namespace Cslib.DataStructure.CellProbe

universe u v z

/-- **Contrapositive Word-RAM lower-bound transfer for certified resource budgets of zero-error
`ObliviousSequenceImpl`s** (standard `w`-bit layout, `0` `η`-loss, no `[Fintype D.Op]`). -/
theorem oblivious_wordRAM_lower_bound_of_det_cellProbe
    {B : Basis} {r_ds k_init w base S_max : ℕ}
    {P : SubroutineCode B r_ds k_init}
    {D : StateTransitionSpec.{u, v, 0}}
    {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    {params : Fin k_init → ℕ} {s₀ : D.State}
    (C : WordRAM.Randomized.ObliviousSequenceImpl.{v, 0, z}
      P (D.toObliviousSequenceSpec s₀) w base params)
    {d₀ : Data r_ds} (hd₀ : d₀.Bounded w)
    (hfr : d₀.regs P.frontierReg = base)
    (hpar : ∀ j, d₀.regs (P.initParams j) = params j)
    (hspace : C.space + persistentRegCount P ≤ S_max)
    (opsAlphabet : Finset D.Op) (M_corr : ℕ)
    (correctSeqs : Set (List D.Op))
    (hcorrectSeqs : ∀ ops ∈ correctSeqs,
      D.ValidHistory s₀ ops ∧ ops.length ≤ M_corr ∧ ∀ o ∈ ops, o ∈ opsAlphabet)
    (hardDist : PMF (List D.Op))
    (hhardDist : ∀ ops ∈ hardDist.support,
      D.ValidHistory s₀ ops ∧ ops.length ≤ M_corr ∧ ∀ o ∈ ops, o ∈ opsAlphabet)
    {LB : ℝ≥0∞}
    (hlb : ∀ D_det : IndexedScheme D.Op D.Result S_max w,
      (∀ ops ∈ correctSeqs, (D_det.runSeq ops).1 = (D.run s₀ ops).2) →
      LB ≤ ∑' ops, hardDist ops * (D_det.seqProbes ops : ℝ≥0∞)) :
    LB ≤ (C.initPotential : ℝ≥0∞) +
      ∑' ops, hardDist ops *
        (((ops.map C.charge).sum : ℝ≥0∞) +
          ((2 * persistentRegCount P : ℕ) : ℝ≥0∞) * (ops.length : ℝ≥0∞)) :=
  lower_bound_of_exists_cellProbeLayout s₀ hspace opsAlphabet M_corr correctSeqs hcorrectSeqs
    hardDist hhardDist _ _ _ (fun _ hη =>
      let ⟨P_raw, hP⟩ := C.exists_cellProbe_lasVegas hd₀ hfr hpar opsAlphabet M_corr hη
      ⟨P_raw,
        fun ops h => (hP ops ((D.validOpSeq_iff_validHistory s₀ ops).mpr (hcorrectSeqs ops h).1)
          (hcorrectSeqs ops h).2.1 (hcorrectSeqs ops h).2.2).1,
        fun ops h => (hP ops ((D.validOpSeq_iff_validHistory s₀ ops).mpr (hhardDist ops h).1)
          (hhardDist ops h).2.1 (hhardDist ops h).2.2).2⟩) hlb

/-- **Wide-cell contrapositive Word-RAM lower-bound transfer for certified resource budgets of
zero-error `ObliviousSequenceImpl`s** (`S_max ≥ C.space + 1` cells of width
`wideSubroutineWidth P w`, at most `2` additive probes per operation regardless of `r_ds`, `0`
`η`-loss, no `[Fintype D.Op]`). -/
theorem oblivious_wordRAM_lower_bound_of_det_cellProbe_wide
    {B : Basis} {r_ds k_init w base S_max : ℕ}
    {P : SubroutineCode B r_ds k_init}
    {D : StateTransitionSpec.{u, v, 0}}
    {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    {params : Fin k_init → ℕ} {s₀ : D.State}
    (C : WordRAM.Randomized.ObliviousSequenceImpl.{v, 0, z}
      P (D.toObliviousSequenceSpec s₀) w base params)
    {d₀ : Data r_ds} (hd₀ : d₀.Bounded w)
    (hfr : d₀.regs P.frontierReg = base)
    (hpar : ∀ j, d₀.regs (P.initParams j) = params j)
    (hspace : C.space + 1 ≤ S_max)
    (opsAlphabet : Finset D.Op) (M_corr : ℕ)
    (correctSeqs : Set (List D.Op))
    (hcorrectSeqs : ∀ ops ∈ correctSeqs,
      D.ValidHistory s₀ ops ∧ ops.length ≤ M_corr ∧ ∀ o ∈ ops, o ∈ opsAlphabet)
    (hardDist : PMF (List D.Op))
    (hhardDist : ∀ ops ∈ hardDist.support,
      D.ValidHistory s₀ ops ∧ ops.length ≤ M_corr ∧ ∀ o ∈ ops, o ∈ opsAlphabet)
    {LB : ℝ≥0∞}
    (hlb : ∀ D_det : IndexedScheme D.Op D.Result S_max (wideSubroutineWidth P w),
      (∀ ops ∈ correctSeqs, (D_det.runSeq ops).1 = (D.run s₀ ops).2) →
      LB ≤ ∑' ops, hardDist ops * (D_det.seqProbes ops : ℝ≥0∞)) :
    LB ≤ (C.initPotential : ℝ≥0∞) +
      ∑' ops, hardDist ops *
        (((ops.map C.charge).sum : ℝ≥0∞) + (2 : ℝ≥0∞) * (ops.length : ℝ≥0∞)) :=
  lower_bound_of_exists_cellProbeLayout s₀ hspace opsAlphabet M_corr correctSeqs hcorrectSeqs
    hardDist hhardDist _ _ (2 : ℝ≥0∞) (fun _ hη =>
      let ⟨P_raw, hP⟩ := C.exists_cellProbeLayout_lasVegas (wideLayout P.input base C.space w)
        hd₀ hfr hpar opsAlphabet M_corr hη
      ⟨P_raw,
        fun ops h => (hP ops ((D.validOpSeq_iff_validHistory s₀ ops).mpr (hcorrectSeqs ops h).1)
          (hcorrectSeqs ops h).2.1 (hcorrectSeqs ops h).2.2).1,
        fun ops h => (hP ops ((D.validOpSeq_iff_validHistory s₀ ops).mpr (hhardDist ops h).1)
          (hhardDist ops h).2.1 (hhardDist ops h).2.2).2.trans (add_le_add le_rfl (mul_le_mul'
            (add_le_add (by rw [wideLayout_overhead]; split_ifs <;> norm_num) le_rfl) le_rfl))⟩)
    hlb

end Cslib.DataStructure.CellProbe
