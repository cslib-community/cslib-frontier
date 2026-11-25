/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Space
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Run
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.Bit
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.Decode
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.PolySpace
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.PolyTime

/-!
# Native visited-space `PSPACE`-completeness of `SPACETM` (after Arora–Barak Exercise 4 §3)

Arora and Barak (2007 draft, Chapter 4, Section 4.3, display (2) on printed p. 79 / PDF p. 95 and
Exercise 4 §3 on printed p. 89 / PDF p. 105) define the canonical space-bounded acceptance problem
$$\mathrm{SPACETM} =
  \{\langle M, w, 1^n \rangle : \text{DTM } M \text{ accepts } w \text{ in space } n\}$$
and show that it is `PSPACE`-complete under polynomial-time many-one reductions.

This module establishes the **native visited-space** formalization of `SPACETM` and its
`PSPACE`-completeness in this repository's multi-tape Turing machine model, where space counts the
number of distinct work-tape cells visited by the work-tape heads during the run
(`Turing.MultiTapeNTM.RunsInSpace` and `Turing.MultiTapeTM.Universal.simSpace`), whereas Arora and
Barak's textbook model counts ever-nonblank cells (see `results/arora-barak-2007.md` row 4.16).

We represent instances as a structured record `Cslib.Complexity.SPACETMInstance` with a machine
description `machine : Desc`, an input bitstring `input : List Bool`, and a space bound
`space : ℕ` encoded in **unary** (`encSPACETMInstance`).

* **Visited-space acceptance (`SPACETMInstance.Accepts`, `SPACETM.desc_mem_iff`):** An instance
  `a : SPACETMInstance` accepts at step `t` when `simSpace a.machine (a.input.map eBit) t ≤ a.space`
  and `universal (a.machine, a.input.map eBit, t) = ([eBit true], true)` — equivalently, when
  the visited-cell-budgeted universal simulator
  `Turing.MultiTapeTM.Universal.spaceBoundedUniversal` returns `([eBit true], true)`. On the
  description `desc eS eBit tm` of any binary machine `tm`, `⟨desc eS eBit tm, x, n⟩ ∈ SPACETM`
  holds unconditionally if and only if at some step `t`, the run path visits at most `n` work-tape
  cells and `tm` has halted on `x` with output `[true]` (`SPACETM.desc_mem_iff`).
* **Configuration-count clock and `PSPACE` membership (`SPACETM.mem_PSPACE`):** Any simulation of
  `a.machine` on `a.input.map eBit` visiting at most `a.space` work-tape cells has configurations
  encoded within `a.cfgBudget = O(|d| · (n + 1) + |x|)` bits
  (`SPACETMInstance.cfgSpaceBound_le_cfgBudget`), so it can visit at most
  `2 ^ (a.cfgBudget + 1) - 1` distinct configurations before repeating a configuration or halting
  (`Turing.MultiTapeTM.Universal.exists_simSpace_le_and_universal_eq_true_iff`). Running
  `spaceBoundedUniversal` for `2 ^ (a.cfgBudget + 1)` steps within visited-cell budget `a.space`
  therefore decides `SPACETM` in polynomial space (`SPACETM.mem_iff_accepts_clock`,
  `SPACETMInstance.computableInPolySpace_decider`).
* **`PSPACE`-hardness and completeness (`SPACETM.pspaceHard`, `SPACETM.pspaceComplete`):** Every
  problem `A ∈ DSPACE enc p` for a polynomial-time unary function `p` reduces to `SPACETM` in
  polynomial time via `a ↦ ⟨desc eS eBit tm, enc a, c₁ * p |enc a| + c₂⟩`
  (`SPACETM.polyTimeReducible`), quantifying over every source type `α` and encoding
  `enc : α ↪ List Bool`. Since `PSPACE enc = ⋃ k, DSPACE enc (· ^ k)`, `SPACETM` is
  `PSPACE`-complete in the native visited-space model.

## Main definitions

* `Cslib.Complexity.SPACETMInstance`, `Cslib.Complexity.encSPACETMInstance`: structured instances
  `(machine, input, space)` with `space` encoded in unary.
* `Cslib.Complexity.SPACETMInstance.cfgBudget`: linear bound on the encoded bit-length of simulated
  configurations visiting at most `space` work-tape cells.
* `Cslib.Complexity.SPACETMInstance.Accepts`, `Cslib.Complexity.SPACETM`: acceptance within the
  visited work-tape cell budget `a.space` and the decision problem `SPACETM`.
* `Cslib.Complexity.SPACETMInstance.decider`: the clocked polynomial-space decider using
  `spaceBoundedUniversal`.

## Main results

* `Cslib.Complexity.SPACETM.mem_iff_accepts_clock`: `a ∈ SPACETM` iff
  `a.Accepts (2 ^ (a.cfgBudget + 1))`.
* `Cslib.Complexity.SPACETM.desc_mem_iff`: on the description of any machine `tm`,
  `⟨desc eS eBit tm, x, n⟩ ∈ SPACETM` iff `tm` halts on `x` with output `[true]` at some step `t`
  whose run path visits at most `n` work-tape cells.
* `Cslib.Complexity.SPACETM.desc_mem_iff_of_runsInSpace`: when `tm.RunsInSpace x n`, membership in
  `SPACETM` is halting with output `[true]`.
* `Cslib.Complexity.SPACETM.mem_PSPACE`: `SPACETM ∈ PSPACE encSPACETMInstance` (native
  visited-space model).
* `Cslib.Complexity.SPACETM.polyTimeReducible`, `Cslib.Complexity.SPACETM.pspaceHard`,
  `Cslib.Complexity.SPACETM.pspaceComplete`: native visited-space `PSPACE`-completeness of
  `SPACETM` under polynomial-time many-one reductions.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach* (2007 draft),
  Chapter 4, Section 4.3, display (2) and Exercise 4 §3][AroraBarak07]
-/

public section

namespace Cslib.Complexity

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.Universal

/-- An instance of the canonical space-bounded acceptance problem `SPACETM` in the native
visited-space model [after Arora and Barak, Chapter 4, Section 4.3, display (2) and
Exercise 4 §3][AroraBarak07]:
* `machine`: a multi-tape Turing machine description `d : Desc`,
* `input`: a binary input word `x : List Bool`,
* `space`: a visited work-tape cell budget `n : ℕ` (encoded in unary by `encSPACETMInstance`). -/
structure SPACETMInstance where
  /-- Description of the simulated deterministic multi-tape machine. -/
  machine : Desc
  /-- Binary input word fed to the machine. -/
  input : List Bool
  /-- Visited work-tape cell budget (encoded in unary). -/
  space : ℕ

/-- Canonical encoding of `SPACETMInstance`: `machine` via `eDesc`, `input` via `encBits`, and
`space` in **unary** (`encUnary`). -/
enc_structure encSPACETMInstance : SPACETMInstance where
  machine : eDesc,
  input : encBits,
  space : encUnary

attribute [fun_prop] encSPACETMInstance_machine_polyTime
  encSPACETMInstance_input_polyTime
  encSPACETMInstance_space_polyTime
  encSPACETMInstance_mk_polyTime
  encSPACETMInstance_space_inO

namespace SPACETMInstance

/-- Total polynomial-time decoder for `encSPACETMInstance`. -/
@[expose] def decoder : Decoder encSPACETMInstance :=
  (Decoder.pair descDecoder (.pair .bits .unary)).map
    (fun ⟨m, x, s⟩ => ⟨m, x, s⟩) (fun a => (a.machine, a.input, a.space))
    (fun _ => rfl) (fun _ => rfl)

/-- Upper bound on the encoded bit-length of any simulated configuration of `a.machine` on
`a.input.map eBit` that visits at most `a.space` work-tape cells
(`Turing.MultiTapeTM.Universal.length_eCfg_le_space`). -/
@[expose] def cfgBudget (a : SPACETMInstance) : ℕ :=
  3 * descLen a.machine + 2 * a.input.length +
    6 * (2 * descLen a.machine + 5) * a.space + 6

/-- The configuration space bound `cfgSpaceBound` for `a.machine` on `a.input.map eBit` within
`a.space` visited work-tape cells is at most `a.cfgBudget`. -/
theorem cfgSpaceBound_le_cfgBudget (a : SPACETMInstance) :
    cfgSpaceBound (descLen a.machine) (a.input.map eBit).length a.machine.tapes a.space ≤
      a.cfgBudget := by
  have := tapes_le a.machine
  have : (encNat ((a.input.map eBit).length + 1)).length ≤ a.input.length + 1 := by
    simpa only [List.length_map] using length_encNat_le_self (a.input.length + 1)
  have : 3 * (2 * descLen a.machine + 5) * 2 * a.space =
      6 * (2 * descLen a.machine + 5) * a.space := by ring
  unfold cfgSpaceBound cfgBudget
  omega

/-- Whenever the simulation of `a.machine` on `a.input.map eBit` up to step `t` visits at most
`a.space` work-tape cells, its configuration space bound `cfgSpace` is at most `a.cfgBudget`. -/
theorem cfgSpace_le_cfgBudget (a : SPACETMInstance) {t : ℕ}
    (hsp : simSpace a.machine (a.input.map eBit) t ≤ a.space) :
    cfgSpace a.machine (a.input.map eBit) t ≤ a.cfgBudget := by
  refine le_trans ?_ a.cfgSpaceBound_le_cfgBudget
  unfold cfgSpace cfgSpaceBound
  gcongr

/-- `a.cfgBudget` is computable in polynomial time in unary from `encSPACETMInstance`. -/
@[fun_prop]
theorem computableInPolyTime_cfgBudget :
    ComputableInPolyTime cfgBudget encSPACETMInstance encUnary := by
  have hmlen : ComputableInPolyTime (fun a : SPACETMInstance => descLen a.machine)
      encSPACETMInstance encUnary :=
    ComputableInPolyTime.length_bits.comp
      ((ComputableInPolyTime.of_eq (encIn := eDesc) (encOut := encBits) fun _ => rfl).comp
        (by fun_prop))
  unfold cfgBudget
  exact ComputableInPolyTime.unary_add'
    (ComputableInPolyTime.unary_add'
      (ComputableInPolyTime.unary_add'
        (ComputableInPolyTime.unary_mul' (.const 3) hmlen)
        (ComputableInPolyTime.unary_mul' (.const 2) (by fun_prop)))
      (ComputableInPolyTime.unary_mul'
        (ComputableInPolyTime.unary_mul' (.const 6)
          (ComputableInPolyTime.unary_add' (ComputableInPolyTime.unary_mul' (.const 2) hmlen)
            (.const 5)))
        (by fun_prop)))
    (.const 6)

/-- Instance `a` accepts at step `t` when the simulation of `a.machine` on `a.input.map eBit` up
to step `t` visits at most `a.space` work-tape cells (`simSpace ≤ a.space`) and has halted with
output `[eBit true]`. -/
@[expose] def Accepts (a : SPACETMInstance) (t : ℕ) : Prop :=
  simSpace a.machine (a.input.map eBit) t ≤ a.space ∧
    universal (a.machine, a.input.map eBit, t) = ([eBit true], true)

instance (a : SPACETMInstance) (t : ℕ) : Decidable (a.Accepts t) :=
  inferInstanceAs (Decidable
    (simSpace a.machine (a.input.map eBit) t ≤ a.space ∧
      universal (a.machine, a.input.map eBit, t) = ([eBit true], true)))

/-- `a.Accepts t` is equivalent to `spaceBoundedUniversal` halting with output `[eBit true]` at
step `t` within visited-cell budget `a.space`. -/
theorem accepts_iff_spaceBoundedUniversal (a : SPACETMInstance) (t : ℕ) :
    a.Accepts t ↔
      spaceBoundedUniversal (a.machine, a.input.map eBit, t, a.space) = ([eBit true], true) :=
  (spaceBoundedUniversal_eq_singleton_true_iff a.machine (a.input.map eBit) t a.space
    (eBit true)).symm

private theorem eq_singleton_true_of_map_eBit {out : List Bool}
    (h : out.map eBit = [eBit true]) : out = [true] :=
  List.map_injective_iff.mpr eBit.injective h

/-- **Unconditional machine-level characterization of `Accepts`:** on the description of any
binary multi-tape machine `tm`, `Accepts ⟨desc eS eBit tm, x, n⟩ t` holds if and only if the run
path of `tm` on `x` up to step `t` visits at most `n` work-tape cells and `tm` has halted on `x`
by step `t` with output `[true]`. -/
theorem accepts_desc_iff {k : ℕ} {State : Type} [Fintype State] (eS : State ↪ ℕ)
    (tm : MultiTapeTM k Bool State) (x : List Bool) (n t : ℕ) :
    Accepts ⟨desc eS eBit tm, x, n⟩ t ↔
      (MultiTapeNTM.RunPath.ofDeterministic tm (tm.initCfg x) t).space ≤ n ∧
        (tm.runFrom (tm.initCfg x) t).Halted ∧
        (tm.runFrom (tm.initCfg x) t).output = [true] := by
  unfold Accepts
  rw [simSpace_desc, universal_desc, Prod.mk.injEq]
  refine and_congr_right' ⟨fun ⟨hout, hhalt⟩ =>
      ⟨Option.isNone_iff_eq_none.mp hhalt, eq_singleton_true_of_map_eBit hout⟩,
    fun ⟨hhalt, hout⟩ => ⟨by rw [hout]; rfl, Option.isNone_iff_eq_none.mpr hhalt⟩⟩

/-- When the simulation up to step `t` visits at most `n` work-tape cells,
`Accepts ⟨desc eS eBit tm, x, n⟩ t` holds if and only if `tm` has halted on `x` by step `t` with
output `[true]`. -/
theorem accepts_desc_iff_of_simSpace_le {k : ℕ} {State : Type} [Fintype State] (eS : State ↪ ℕ)
    (tm : MultiTapeTM k Bool State) (x : List Bool) (n t : ℕ)
    (hsp : simSpace (desc eS eBit tm) (x.map eBit) t ≤ n) :
    Accepts ⟨desc eS eBit tm, x, n⟩ t ↔
      (tm.runFrom (tm.initCfg x) t).Halted ∧
        (tm.runFrom (tm.initCfg x) t).output = [true] := by
  rw [accepts_desc_iff]
  exact and_iff_right (simSpace_desc eS eBit tm x t ▸ hsp)

/-- Clocked Boolean decider for `SPACETM`: run `spaceBoundedUniversal` for `2 ^ (a.cfgBudget + 1)`
steps within visited work-tape cell budget `a.space` and test whether the result is
`([eBit true], true)`. -/
@[expose] def decider (a : SPACETMInstance) : Bool :=
  decide (spaceBoundedUniversal (a.machine, a.input.map eBit, 2 ^ (a.cfgBudget + 1),
    a.space) = ([eBit true], true))

/-- The clocked decider `SPACETMInstance.decider` is computable in polynomial space. -/
theorem computableInPolySpace_decider :
    ComputableInPolySpace decider encSPACETMInstance encBool := by
  have hmap : ComputableInPolyTime (fun a : SPACETMInstance => a.input.map eBit)
      encSPACETMInstance (encList encUnary) := computableInPolyTime_map_eBit.comp (by fun_prop)
  have hclock : ComputableInPolyTime (fun a : SPACETMInstance => 2 ^ (a.cfgBudget + 1))
      encSPACETMInstance encNat := ComputableInPolyTime.binary_two_pow.comp (by fun_prop)
  have hout : ComputableInPolyTime
      (fun r : List ℕ × Bool => decide (r = ([eBit true], true))) eOut encBool := by
    unfold eOut
    fun_prop
  have hin : ComputableInPolyTime
      (fun a : SPACETMInstance => (a.machine, a.input.map eBit, 2 ^ (a.cfgBudget + 1), a.space))
      encSPACETMInstance eInS := by
    unfold eInS
    fun_prop
  exact (ComputableInPolySpace.of_polyTime hout).comp
    (computableInPolySpace_spaceBoundedUniversal.comp (ComputableInPolySpace.of_polyTime hin))

end SPACETMInstance

/-- **Canonical space-bounded Turing machine acceptance (`SPACETM`) in the native visited-space
model** [after Arora and Barak, Chapter 4, Section 4.3, display (2) and
Exercise 4 §3][AroraBarak07]:
the instances `a : SPACETMInstance` for which the simulation of `a.machine` on `a.input` halts with
output `[eBit true]` at some step `t` while visiting at most `a.space` work-tape cells. -/
@[expose] def SPACETM : Set SPACETMInstance :=
  {a | ∃ t : ℕ, a.Accepts t}

namespace SPACETM

theorem mem_iff {a : SPACETMInstance} : a ∈ SPACETM ↔ ∃ t : ℕ, a.Accepts t :=
  Iff.rfl

/-- **`SPACETM` is equivalent to acceptance at the configuration-count clock
`2 ^ (a.cfgBudget + 1)`.** -/
theorem mem_iff_accepts_clock (a : SPACETMInstance) :
    a ∈ SPACETM ↔ a.Accepts (2 ^ (a.cfgBudget + 1)) :=
  exists_simSpace_le_and_universal_eq_true_iff a.machine (a.input.map eBit) a.space [eBit true]
    a.cfgSpaceBound_le_cfgBudget le_rfl

/-- **`SPACETM` is decided by `SPACETMInstance.decider`.** -/
theorem mem_iff_decider (a : SPACETMInstance) :
    a ∈ SPACETM ↔ a.decider = true := by
  rw [mem_iff_accepts_clock, SPACETMInstance.decider, decide_eq_true_eq,
    SPACETMInstance.accepts_iff_spaceBoundedUniversal]

/-- **Unconditional machine-level characterization of `SPACETM`:** on the description of any binary
multi-tape machine `tm`, `⟨desc eS eBit tm, x, n⟩ ∈ SPACETM` holds if and only if at some step `t`,
the run path of `tm` on `x` visits at most `n` work-tape cells and `tm` has halted on `x` with
output `[true]`. -/
theorem desc_mem_iff {k : ℕ} {State : Type} [Fintype State] (eS : State ↪ ℕ)
    (tm : MultiTapeTM k Bool State) (x : List Bool) (n : ℕ) :
    ⟨desc eS eBit tm, x, n⟩ ∈ SPACETM ↔
      ∃ t, (MultiTapeNTM.RunPath.ofDeterministic tm (tm.initCfg x) t).space ≤ n ∧
        (tm.runFrom (tm.initCfg x) t).Halted ∧
        (tm.runFrom (tm.initCfg x) t).output = [true] :=
  exists_congr fun t => SPACETMInstance.accepts_desc_iff eS tm x n t

/-- **On the description of a machine `tm` that visits at most `n` work-tape cells on `x`**
(`tm.RunsInSpace x n`), `⟨desc eS eBit tm, x, n⟩ ∈ SPACETM` holds if and only if `tm` halts on `x`
with output `[true]`. -/
theorem desc_mem_iff_of_runsInSpace {k : ℕ} {State : Type} [Fintype State] (eS : State ↪ ℕ)
    (tm : MultiTapeTM k Bool State) (x : List Bool) (n : ℕ) (hsp : tm.RunsInSpace x n) :
    ⟨desc eS eBit tm, x, n⟩ ∈ SPACETM ↔
      ∃ t, (tm.runFrom (tm.initCfg x) t).Halted ∧
        (tm.runFrom (tm.initCfg x) t).output = [true] :=
  (desc_mem_iff eS tm x n).trans
    (exists_congr fun t => and_iff_right (space_le_of_runsInSpace hsp t))

/-- **`SPACETM` is in `PSPACE`** in the native visited-space model (after Arora–Barak
Exercise 4 §3, membership). -/
theorem mem_PSPACE : SPACETM ∈ PSPACE encSPACETMInstance :=
  ⟨SPACETMInstance.decider, SPACETMInstance.computableInPolySpace_decider, mem_iff_decider⟩

/-- **Space-bounded problems reduce to `SPACETM`.** Every problem decided within visited work-tape
space `c₁ * p |enc a| + c₂` for a polynomial-time unary function `p` reduces to `SPACETM` in
polynomial time via `a ↦ ⟨desc eS eBit tm, enc a, c₁ * p |enc a| + c₂⟩`. -/
theorem polyTimeReducible {α : Type} {enc : α ↪ List Bool} {A : Set α} {p : ℕ → ℕ}
    (hp : ComputableInPolyTime p encUnary encUnary) {c₁ c₂ : ℕ} {t : α → ℕ}
    (hA : DecidableInTimeAndSpace A enc t (fun a => c₁ * p (enc a).length + c₂)) :
    PolyTimeReducible enc encSPACETMInstance A SPACETM := by
  obtain ⟨g, ⟨k, State, _, tm, htm⟩, hg⟩ := decidableInTimeAndSpace_iff.mp hA
  have := Fintype.ofFinite State
  let eS : State ↪ ℕ := (Fintype.equivFin State).toEmbedding.trans Fin.valEmbedding
  refine ⟨fun a => ⟨desc eS eBit tm, enc a, c₁ * p (enc a).length + c₂⟩, ?_, fun a => ?_⟩
  · have : ComputableInPolyTime (fun a => p (enc a).length) enc encUnary :=
      hp.comp (ComputableInPolyTime.length_bits.comp (.of_eq fun _ => rfl))
    fun_prop
  · rw [desc_mem_iff_of_runsInSpace eS tm (enc a) _ (htm a).2.2, hg]
    obtain ⟨hhalt, hout : (tm.runFrom (tm.initCfg (enc a)) (t a)).output = [g a]⟩ :=
      (htm a).runFrom_of_le le_rfl
    refine ⟨fun h => ⟨t a, hhalt, hout.trans (congrArg (· :: []) h)⟩,
      fun ⟨t', hhalt', hout'⟩ => ?_⟩
    have heq : (tm.runFrom (tm.initCfg (enc a)) (t a)).output =
        (tm.runFrom (tm.initCfg (enc a)) t').output :=
      (le_total t' (t a)).elim
        (fun hle => congrArg Cfg.output (tm.runFrom_eq_of_halt _ hle hhalt'))
        (fun hle => (congrArg Cfg.output (tm.runFrom_eq_of_halt _ hle hhalt)).symm)
    exact List.cons.inj (hout.symm.trans (heq.trans hout')) |>.1

/-- **`SPACETM` is `PSPACE`-hard** in the native visited-space model under polynomial-time many-one
reductions, quantifying over every source type `α` and encoding `enc : α ↪ List Bool`
(after Arora–Barak Exercise 4 §3, hardness). -/
theorem pspaceHard : PSPACEHard encSPACETMInstance SPACETM := fun _ _ _ hA =>
  let ⟨k, _, _, _, hdec⟩ := mem_PSPACE_iff_exists_mem_DSPACE.mp hA
  polyTimeReducible (p := (· ^ k)) (by fun_prop) hdec

/-- **`SPACETM` is `PSPACE`-complete** in the native visited-space model under polynomial-time
many-one reductions (after Arora–Barak Chapter 4, display (2) and Exercise 4 §3). -/
theorem pspaceComplete : PSPACEComplete encSPACETMInstance SPACETM :=
  ⟨mem_PSPACE, pspaceHard⟩

end SPACETM

end Cslib.Complexity
