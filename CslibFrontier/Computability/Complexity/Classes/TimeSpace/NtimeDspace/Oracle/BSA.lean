/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Doubled
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Composition.Recompute
public import CslibFrontier.Computability.Machines.Turing.MultiTape.HaltsAt
public import CslibFrontier.Computability.Machines.Turing.MultiTape.TapeLemmas
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.Bit
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.Complexity
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.Decode
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.InPlace
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.SpaceBudget
import CslibFrontier.Computability.Machines.Turing.MultiTape.Run

/-!
# The bounded space acceptance oracle `BSA`

Machines are given by Complexitylib's descriptions `Turing.MultiTapeTM.Universal.Desc` (any number
of work tapes, states and symbols numbered in `ℕ`), run by Complexitylib's universal simulation
`Turing.MultiTapeTM.Universal.run`/`simulate`, and every word `w` describes the machine
`Turing.MultiTapeTM.Universal.decodeDesc w`. The machine described by `d` **accepts `x` within
space `b`** (`AcceptsWithin d x b`) when its run on `x` halts with output `[1]` (the bit `true`)
and every configuration reached by a step has a description (`Turing.MultiTapeTM.Universal.eCfg`:
the state, the input head in binary and the zippers of the work tapes) of at most `b` bits.

The oracle is
`BSA = {frame w ++ frame x ++ 1^b : 2^|w| ≤ b and decodeDesc w accepts x within space b}`,
the strings `⟨M'⟩ # x # 1^b` of Remark 8.3, with `frame` (each bit `c` as `[true, c]`, then
`[false]`) as the separator `#`.

## Relation to the paper

This is the paper's definition (Remark 8.3): `M'` ranges over deterministic multitape machines,
and "accepts `x` in space `b`" means that every configuration it reaches, described by its state,
its input head position in binary and its visited work cells, has a description of at most `b`
bits. It gives the two properties the remark uses: a query is answerable in space linear in its
length, and every machine deciding a language in linear space, with any number of tapes, is
described
(`acceptsWithin_desc_iff`). The condition `2^|w| ≤ b` only pads the budget, so that decoding
the description `w`, which Complexitylib does within polynomial (not linear) bounds, fits in space
`O(b)`; a fixed machine meets it for all long enough budgets.

## Main definitions

* `Cslib.Complexity.NtimeDspace.Oracle.AcceptsWithin`: acceptance within space `b`.
* `Cslib.Complexity.NtimeDspace.Oracle.bsaQuery`: the query `⟨M'⟩ # x # 1^b`.
* `Cslib.Complexity.NtimeDspace.Oracle.BSA`: the oracle.

## Main results

* `Cslib.Complexity.NtimeDspace.Oracle.bsaQuery_mem_BSA_iff`: membership of a query.
* `Cslib.Complexity.NtimeDspace.Oracle.acceptsWithin_desc_iff`: a machine computing the indicator of
`L` within
  space `s` accepts `x` within any budget above its configuration bound exactly when `x ∈ L`.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Oracle

open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapeTM.Universal

/-- The machine described by `d` accepts `x` within space `b`: its run on `x` halts with output
`[1]` after some number `T` of steps, and every configuration reached by a step before then is
described by at most `b` bits. -/
def AcceptsWithin (d : Desc) (x : List ℕ) (b : ℕ) : Prop :=
  ∃ T, simulate d x T = ([1], true) ∧ ∀ j < T, (eCfg (run d x (j + 1))).length ≤ b

/-- The query `⟨M'⟩ # x # 1^b`. -/
def bsaQuery (w x : List Bool) (b : ℕ) : List Bool :=
  frame w ++ frame x ++ List.replicate b true

/-- **The oracle `BSA`** (bounded space acceptance): the queries `⟨M'⟩ # x # 1^b` such that the
machine described by `M'` accepts `x` within space `b`, with the padding `2^|M'| ≤ b`. -/
def BSA : Set (List Bool) :=
  {q | ∃ w x b, q = bsaQuery w x b ∧ 2 ^ w.length ≤ b ∧
    AcceptsWithin (decodeDesc w) (x.map eBit) b}

lemma bsaQuery_inj {w x w' x' : List Bool} {b b' : ℕ} (h : bsaQuery w x b = bsaQuery w' x' b') :
    w = w' ∧ x = x' ∧ b = b' := by
  unfold bsaQuery at h
  rw [List.append_assoc, List.append_assoc] at h
  obtain ⟨h1, h⟩ := frame_append_inj h
  obtain ⟨h2, h⟩ := frame_append_inj h
  exact ⟨h1, h2, by simpa using congrArg List.length h⟩

lemma bsaQuery_mem_BSA_iff {w x : List Bool} {b : ℕ} :
    bsaQuery w x b ∈ BSA ↔ 2 ^ w.length ≤ b ∧ AcceptsWithin (decodeDesc w) (x.map eBit) b := by
  constructor
  · rintro ⟨w', x', b', h, hb, ha⟩
    obtain ⟨rfl, rfl, rfl⟩ := bsaQuery_inj h
    exact ⟨hb, ha⟩
  · rintro ⟨hb, ha⟩
    exact ⟨w, x, b, rfl, hb, ha⟩

lemma length_bsaQuery (w x : List Bool) (b : ℕ) :
    (bsaQuery w x b).length = 2 * w.length + 1 + (2 * x.length + 1) + b := by
  simp [bsaQuery]
  omega

/-- The bound on the description of the configurations of the simulation of a machine with
description `d` on an input of length `n`, using `s` work cells. -/
def cfgBudget (d : Desc) (n s : ℕ) : ℕ :=
  2 * descLen d + 3 + 2 * (encNat (n + 1)).length + 1 + 3 * (2 * descLen d + 5) * 2 * s + d.tapes

/-- **Machines deciding a language are described.** If `tm` computes the indicator of `L` on `x`
within space `s`, then its description accepts `x` within every budget `b` above
`cfgBudget (desc eS eBit tm) |x| s` exactly when `x ∈ L`. -/
theorem acceptsWithin_desc_iff {k : ℕ} {State : Type} [Fintype State] (eS : State ↪ ℕ)
    (tm : MultiTapeTM k Bool State) {L : Set (List Bool)} {x : List Bool} {t s b : ℕ}
    (htm : tm.ComputesInTimeAndSpace x [indicator L x] t s)
    (hb : cfgBudget (desc eS eBit tm) x.length s ≤ b) :
    AcceptsWithin (desc eS eBit tm) (x.map eBit) b ↔ x ∈ L := by
  obtain ⟨⟨u, hu, hout⟩, -, hs⟩ := htm
  constructor
  · rintro ⟨T, hT, -⟩
    rw [simulate_desc] at hT
    simp only [Prod.mk.injEq, Option.isNone_iff_eq_none] at hT
    have e₁ := tm.runFrom_eq_of_halt (tm.initCfg x) (le_max_left T u) hT.2
    have e₂ := tm.runFrom_eq_of_halt (tm.initCfg x) (le_max_right T u) hu
    rw [← e₁, e₂, hout] at hT
    have h1 : eBit (indicator L x) = 1 := by simpa using hT.1
    by_contra hx
    simp only [indicator, hx, ite_false] at h1
    exact absurd h1 (by decide)
  · intro hx
    refine ⟨u, ?_, fun j _ => ?_⟩
    · rw [simulate_desc, hout]
      simp only [Cfg.Halted] at hu
      simp only [indicator, hx, ite_true, List.map_cons, List.map_nil, hu, Option.isNone_none]
      rfl
    · refine (length_eCfg_le_space _ _ (j + 1)).trans (le_trans ?_ hb)
      have hsp := space_le_of_runsInSpace hs (j + 1)
      rw [← simSpace_desc] at hsp
      simp only [cfgBudget, List.length_map]
      gcongr

end Cslib.Complexity.NtimeDspace.Oracle
