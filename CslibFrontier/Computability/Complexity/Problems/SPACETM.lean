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
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.SpaceBudget
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolySpace.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.PolyTime
import CslibFrontier.Foundations.Data.BitString.ShortWords

/-!
# `SPACETM` is `PSPACE`-complete (Arora–Barak Exercise 4 §3)

Arora and Barak (2007 draft, Chapter 4, display (2) on printed p. 81 / PDF p. 97 and Exercise 4 §3
on printed p. 89 / PDF p. 105) define the canonical space-bounded acceptance problem
$$\mathrm{SPACETM} =
  \{\langle M, w, 1^n \rangle : \text{DTM } M \text{ accepts } w \text{ in space } n\}$$
and show that it is `PSPACE`-complete under polynomial-time many-one reductions.

We represent instances as a structured record `Cslib.Complexity.SPACETMInstance` with a machine
description `machine : Desc`, an input bitstring `input : List Bool`, and a space bound
`space : ℕ` encoded in **unary** (`encSPACETMInstance`).

* **Space measure qualification:** In this repository (`Turing.MultiTapeNTM.RunsInSpace` and
  `Turing.MultiTapeTM.Universal.simSpace`), space counts the number of distinct work-tape cells
  visited by the work-tape heads during the run, whereas Arora and Barak's textbook model counts
  ever-nonblank cells (see `results/arora-barak-2007.md` row 4.16). On the description
  `desc eS eBit tm` of a machine `tm` that visits at most `n` work-tape cells on `x`
  (`tm.RunsInSpace x n`), every simulated configuration is encoded within
  `a.cfgBudget = O(|d| · (n + 1) + |x|)` bits (`SPACETMInstance.cfgSpace_le_cfgBudget`), so the
  budgeted universal simulator `Turing.MultiTapeTM.Universal.budgetedUniversal` faithfully follows
  every step of `tm` on `x` (`SPACETM.desc_mem_iff_of_runsInSpace`).
* **Configuration-count clock and `PSPACE` membership (`SPACETM.mem_PSPACE`):** A space-budgeted
  simulation `budgetedUniversal (d, x, t, b)` can visit at most `2 ^ (b + 1) - 1` distinct encoded
  configurations of length at most `b` (`Cslib.BitString.shortWords b`) before repeating a
  configuration or halting (`Turing.MultiTapeTM.Universal.exists_budgetedUniversal_eq_true_iff`).
  Running `budgetedUniversal` for `2 ^ (a.cfgBudget + 1)` steps therefore decides whether the
  budgeted simulation ever halts and accepts (`SPACETM.mem_iff_accepts_clock`), rejecting machines
  that loop or exceed the configuration budget while using space linear in `a.cfgBudget + |a|`.
* **`PSPACE`-hardness and completeness (`SPACETM.pspaceHard`, `SPACETM.pspaceComplete`):** Every
  problem `A ∈ DSPACE enc p` for a polynomial-time unary function `p` reduces to `SPACETM` in
  polynomial time via `a ↦ ⟨desc eS eBit tm, enc a, c₁ * p |enc a| + c₂⟩`
  (`SPACETM.polyTimeReducible`), quantifying over every source type `α` and encoding
  `enc : α ↪ List Bool`. Since `PSPACE enc = ⋃ k, DSPACE enc (· ^ k)`, `SPACETM` is
  `PSPACE`-complete.

## Main definitions

* `Cslib.Complexity.SPACETMInstance`, `Cslib.Complexity.encSPACETMInstance`: structured instances
  `(machine, input, space)` with `space` encoded in unary.
* `Cslib.Complexity.SPACETMInstance.cfgBudget`: linear bound on the encoded bit-length of simulated
  configurations visiting at most `space` work-tape cells.
* `Cslib.Complexity.SPACETMInstance.Accepts`, `Cslib.Complexity.SPACETM`: acceptance within the
  space budget and the decision problem `SPACETM`.
* `Cslib.Complexity.SPACETMInstance.decider`: the clocked polynomial-space decider.

## Main results

* `Turing.MultiTapeTM.Universal.exists_budgetedUniversal_eq_true_iff`: a budgeted simulation halts
  with a given output at some step if and only if it has halted with that output by step
  `2 ^ (b + 1)`.
* `Turing.MultiTapeTM.Universal.computableInPolySpace_budgetedUniversal`: `budgetedUniversal` is
  computable in polynomial space.
* `Cslib.Complexity.SPACETM.mem_iff_accepts_clock`: `a ∈ SPACETM` iff
  `a.Accepts (2 ^ (a.cfgBudget + 1))`.
* `Cslib.Complexity.SPACETM.desc_mem_iff_of_runsInSpace`: on the description of a machine `tm` with
  `tm.RunsInSpace x n`, membership in `SPACETM` is halting with output `[true]`.
* `Cslib.Complexity.SPACETM.mem_PSPACE`: `SPACETM ∈ PSPACE encSPACETMInstance`.
* `Cslib.Complexity.SPACETM.polyTimeReducible`, `Cslib.Complexity.SPACETM.pspaceHard`,
  `Cslib.Complexity.SPACETM.pspaceComplete`: `SPACETM` is `PSPACE`-complete under polynomial-time
  many-one reductions.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach* (2007 draft),
  Chapter 4, display (2) and Exercise 4 §3][AroraBarak07]
-/

@[expose] public section

namespace Turing.MultiTapeTM.Universal

open Cslib.BitString

variable (d : Desc) (x : List ℕ) (b : ℕ)

/-- Iterating `fun c => (step d x c).1` from `run d x j` advances `run d x` by `m` steps. -/
theorem step_fst_iterate_run (j m : ℕ) :
    (fun c => (step d x c).1)^[m] (run d x j) = run d x (j + m) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, ← Nat.add_assoc, ← run_succ]

/-- Once `budgetStep` reaches a halted configuration with at most `2` output symbols, it is a fixed
point. -/
theorem budgetStep_of_state_eq_none {p : SCfg × List ℕ} (hstate : p.1.state = none)
    (hlen : p.2.length ≤ 2) : budgetStep d x b p = p := by
  rcases p with ⟨c, out⟩
  dsimp only at hstate hlen
  simp only [budgetStep, step, hstate, Option.toList_none, List.append_nil,
    List.take_of_length_le hlen, ite_self]

/-- Once the budgeted run from `(init d, [])` halts at step `t`, it remains at the same pair at
every later step `T ≥ t`. -/
theorem budgetStep_iterate_eq_of_le {t T : ℕ}
    (hhalt : ((budgetStep d x b)^[t] (init d, [])).1.state.isNone = true) (hT : t ≤ T) :
    (budgetStep d x b)^[T] (init d, []) = (budgetStep d x b)^[t] (init d, []) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hT
  clear hT
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [← Nat.add_assoc, Function.iterate_succ_apply', ih]
    refine budgetStep_of_state_eq_none d x b (Option.isNone_iff_eq_none.mp hhalt) ?_
    obtain ⟨j, -, heq, -⟩ := budgetStep_iterate d x b t
    rw [heq, List.length_take]
    exact min_le_left _ _

/-- Once `budgetedUniversal (d, x, t, b)` reports halting, increasing the step count `t ≤ T` leaves
its result unchanged. -/
theorem budgetedUniversal_eq_of_le_of_snd {t T : ℕ}
    (hhalt : (budgetedUniversal (d, x, t, b)).2 = true) (hT : t ≤ T) :
    budgetedUniversal (d, x, T, b) = budgetedUniversal (d, x, t, b) := by
  simp only [budgetedUniversal] at hhalt ⊢
  rw [budgetStep_iterate_eq_of_le d x b hhalt hT]

/-- **Configuration-count clock for `budgetedUniversal`:** if `budgetedUniversal (d, x, t, b)`
halts at some step `t`, then it already halts with the same output at some step `t₀ ≤ 2 ^ (b + 1)`.
Before the first halting step `t₀`, every step must fit within the `b`-bit configuration budget and
visit a distinct configuration in `shortWords b`. -/
theorem exists_budgetedUniversal_le_two_pow {t : ℕ}
    (hhalt : (budgetedUniversal (d, x, t, b)).2 = true) :
    ∃ t₀ ≤ 2 ^ (b + 1), budgetedUniversal (d, x, t₀, b) = budgetedUniversal (d, x, t, b) := by
  classical
  have hex : ∃ k, ((budgetStep d x b)^[k] (init d, [])).1.state.isNone = true := ⟨t, hhalt⟩
  let t₀ := Nat.find hex
  have ht₀ : ((budgetStep d x b)^[t₀] (init d, [])).1.state.isNone = true := Nat.find_spec hex
  have ht₀_le : t₀ ≤ t := Nat.find_min' hex hhalt
  -- Every step before `t₀` must pass the budget check; otherwise `budgetStep` would be a fixed
  -- point and `t₀` could not be reached.
  have hstep :
      ∀ k < t₀, (eCfg (step d x ((budgetStep d x b)^[k] (init d, [])).1).1).length ≤ b := by
    intro k hk
    by_contra hnot
    have hfix : budgetStep d x b ((budgetStep d x b)^[k] (init d, [])) =
        (budgetStep d x b)^[k] (init d, []) := by
      unfold budgetStep
      split_ifs with h
      · exact absurd h hnot
      · rfl
    have hstay : (budgetStep d x b)^[t₀] (init d, []) =
        (budgetStep d x b)^[k] (init d, []) := by
      rw [← Nat.sub_add_cancel hk.le, Function.iterate_add_apply,
        Function.iterate_fixed hfix (t₀ - k)]
    have hk_halt : ((budgetStep d x b)^[k] (init d, [])).1.state.isNone = true := by
      rwa [← hstay]
    exact Nat.find_min hex hk hk_halt
  have hfst : ∀ k ≤ t₀, ((budgetStep d x b)^[k] (init d, [])).1 = run d x k := by
    intro k hk
    induction k with
    | zero => rfl
    | succ k ih =>
      have hk_lt : k < t₀ := Nat.lt_of_succ_le hk
      have hle := hstep k hk_lt
      rw [Function.iterate_succ_apply', budgetStep]
      split_ifs
      rw [ih hk_lt.le, run_succ]
  have hb : ∀ k < t₀, (eCfg (run d x (k + 1))).length ≤ b := by
    intro k hk
    have hle := hstep k hk
    rwa [hfst k hk.le, ← run_succ] at hle
  have hlt_false : ∀ {i j}, i < j → j < t₀ → run d x (i + 1) = run d x (j + 1) → False := by
    intro i j hlt hj hcfg
    have hshift : run d x (i + 1 + (t₀ - (j + 1))) = run d x t₀ := by
      rw [← step_fst_iterate_run d x (i + 1), hcfg, step_fst_iterate_run d x (j + 1),
        Nat.add_sub_of_le (by omega)]
    have hlt_t₀ : i + 1 + (t₀ - (j + 1)) < t₀ := by omega
    have hearly : ((budgetStep d x b)^[i + 1 + (t₀ - (j + 1))] (init d, [])).1.state.isNone =
        true := by
      rw [hfst _ hlt_t₀.le, hshift, ← hfst t₀ le_rfl]
      exact ht₀
    exact Nat.find_min hex hlt_t₀ hearly
  have hinj : Set.InjOn (fun k => eCfg (run d x (k + 1))) ↑(Finset.range t₀) := by
    intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    rcases lt_trichotomy i j with hlt | rfl | hgt
    · exact False.elim (hlt_false hlt hj (eCfg.injective hij))
    · rfl
    · exact False.elim (hlt_false hgt hi (eCfg.injective hij.symm))
  have hsub : (Finset.range t₀).image (fun k => eCfg (run d x (k + 1))) ⊆ shortWords b := by
    intro w hw
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hw
    exact mem_shortWords.mpr (hb k (Finset.mem_range.mp hk))
  have hcard : t₀ ≤ 2 ^ (b + 1) := by
    calc t₀ = (Finset.range t₀).card := (Finset.card_range t₀).symm
      _ = ((Finset.range t₀).image (fun k => eCfg (run d x (k + 1)))).card :=
        (Finset.card_image_of_injOn hinj).symm
      _ ≤ (shortWords b).card := Finset.card_le_card hsub
      _ ≤ 2 ^ (b + 1) := (card_shortWords_lt b).le
  exact ⟨t₀, hcard, (budgetedUniversal_eq_of_le_of_snd d x b ht₀ ht₀_le).symm⟩

/-- **Clocked equivalence for `budgetedUniversal`:** for any step count `T ≥ 2 ^ (b + 1)`, there
exists a step `t` at which `budgetedUniversal (d, x, t, b) = (out, true)` if and only if
`budgetedUniversal (d, x, T, b) = (out, true)`. -/
theorem exists_budgetedUniversal_eq_true_iff (out : List ℕ) {T : ℕ} (hT : 2 ^ (b + 1) ≤ T) :
    (∃ t, budgetedUniversal (d, x, t, b) = (out, true)) ↔
      budgetedUniversal (d, x, T, b) = (out, true) := by
  refine ⟨fun ⟨t, ht⟩ => ?_, fun h => ⟨T, h⟩⟩
  have hhalt : (budgetedUniversal (d, x, t, b)).2 = true := by rw [ht]
  obtain ⟨t₀, ht₀_le, ht₀_eq⟩ := exists_budgetedUniversal_le_two_pow d x b hhalt
  rw [← ht, ← ht₀_eq]
  exact budgetedUniversal_eq_of_le_of_snd d x b (by rw [ht₀_eq, ht]) (ht₀_le.trans hT)

private lemma listMax_le_length_encList_encUnary (x : List ℕ) :
    x.foldr max 0 ≤ (encList encUnary x).length := by
  induction x with
  | nil => rfl
  | cons a x ih =>
    simp only [List.foldr_cons, encList_cons, List.length_append, length_frame, encUnary_apply,
      List.length_replicate]
    omega

/-- **`budgetedUniversal` is computable in polynomial space** (in fact linear space) with respect
to `eInS` and `eOut`. -/
theorem computableInPolySpace_budgetedUniversal :
    ComputableInPolySpace budgetedUniversal eInS eOut := by
  obtain ⟨c, hc, hl⟩ := computableTidilyInO_budgetedUniversal.computableInO
  refine ComputableInPolySpace.of_inSpace
    (PolyBounded.of_forall_le 76 1 fun ⟨d, x, t, b⟩ => ?_) ⟨_, c, hc, hl⟩
  have hB := budgetSpace_le d x b t
  have hxlen : x.length ≤ (encList encUnary x).length := length_le_length_encList encUnary x
  have hnat : (encNat (x.length + 1)).length ≤ x.length + 1 := length_encNat_le_self (x.length + 1)
  have hmax : x.foldr max 0 ≤ (encList encUnary x).length := listMax_le_length_encList_encUnary x
  simp only [eInS, length_encPair, encUnary_apply, List.length_replicate, descLen, pow_one] at hB ⊢
  omega

end Turing.MultiTapeTM.Universal

namespace Cslib.Complexity

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.Universal

/-- An instance of the canonical space-bounded acceptance problem `SPACETM`
[Arora and Barak, Chapter 4, display (2) and Exercise 4 §3][AroraBarak07]:
* `machine`: a multi-tape Turing machine description `d : Desc`,
* `input`: a binary input word `x : List Bool`,
* `space`: a work-tape space bound `n : ℕ` (encoded in unary by `encSPACETMInstance`). -/
structure SPACETMInstance where
  /-- Description of the simulated deterministic multi-tape machine. -/
  machine : Desc
  /-- Binary input word fed to the machine. -/
  input : List Bool
  /-- Work-tape cell budget (encoded in unary). -/
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
def decoder : Decoder encSPACETMInstance :=
  (Decoder.pair descDecoder (.pair .bits .unary)).map
    (fun ⟨m, x, s⟩ => ⟨m, x, s⟩) (fun a => (a.machine, a.input, a.space))
    (fun _ => rfl) (fun _ => rfl)

/-- Upper bound on the encoded bit-length of any simulated configuration of `a.machine` on
`a.input.map eBit` that visits at most `a.space` work-tape cells
(`Turing.MultiTapeTM.Universal.length_eCfg_le_space`). -/
def cfgBudget (a : SPACETMInstance) : ℕ :=
  3 * descLen a.machine + 2 * a.input.length +
    6 * (2 * descLen a.machine + 5) * a.space + 6

/-- Whenever the simulation of `a.machine` on `a.input.map eBit` up to step `t` visits at most
`a.space` work-tape cells, its configuration space bound `cfgSpace` is at most `a.cfgBudget`. -/
theorem cfgSpace_le_cfgBudget (a : SPACETMInstance) {t : ℕ}
    (hsp : simSpace a.machine (a.input.map eBit) t ≤ a.space) :
    cfgSpace a.machine (a.input.map eBit) t ≤ a.cfgBudget := by
  have htapes : a.machine.tapes ≤ descLen a.machine := tapes_le a.machine
  have hlen : (encNat ((a.input.map eBit).length + 1)).length ≤ a.input.length + 1 := by
    rw [List.length_map]
    exact length_encNat_le_self (a.input.length + 1)
  have hmul : 3 * (2 * descLen a.machine + 5) * 2 * simSpace a.machine (a.input.map eBit) t ≤
      6 * (2 * descLen a.machine + 5) * a.space := by
    calc 3 * (2 * descLen a.machine + 5) * 2 * simSpace a.machine (a.input.map eBit) t
      _ = 6 * (2 * descLen a.machine + 5) * simSpace a.machine (a.input.map eBit) t := by ring
      _ ≤ 6 * (2 * descLen a.machine + 5) * a.space := Nat.mul_le_mul_left _ hsp
  unfold cfgSpace cfgBudget
  omega

/-- `a.cfgBudget` is computable in polynomial time in unary from `encSPACETMInstance`. -/
@[fun_prop]
theorem computableInPolyTime_cfgBudget :
    ComputableInPolyTime cfgBudget encSPACETMInstance encUnary := by
  have hdesc_id : ComputableInPolyTime (fun d : Desc => eDesc d) eDesc encBits :=
    ComputableInPolyTime.of_eq (f := fun d : Desc => eDesc d)
      (encIn := eDesc) (encOut := encBits) fun _ => rfl
  have hmlen : ComputableInPolyTime (fun a : SPACETMInstance => descLen a.machine)
      encSPACETMInstance encUnary :=
    ComputableInPolyTime.length_bits.comp (hdesc_id.comp (encSPACETMInstance_machine_polyTime .id'))
  have hilen : ComputableInPolyTime (fun a : SPACETMInstance => a.input.length)
      encSPACETMInstance encUnary :=
    ComputableInPolyTime.length_bits.comp (encSPACETMInstance_input_polyTime .id')
  have hspace : ComputableInPolyTime (fun a : SPACETMInstance => a.space)
      encSPACETMInstance encUnary :=
    encSPACETMInstance_space_polyTime .id'
  have h2m5 : ComputableInPolyTime (fun a : SPACETMInstance => 2 * descLen a.machine + 5)
      encSPACETMInstance encUnary :=
    ComputableInPolyTime.unary_add' (ComputableInPolyTime.unary_mul' (.const 2) hmlen) (.const 5)
  have hterm1 : ComputableInPolyTime
      (fun a : SPACETMInstance => 3 * descLen a.machine + 2 * a.input.length)
      encSPACETMInstance encUnary :=
    ComputableInPolyTime.unary_add'
      (ComputableInPolyTime.unary_mul' (.const 3) hmlen)
      (ComputableInPolyTime.unary_mul' (.const 2) hilen)
  have hterm2 : ComputableInPolyTime
      (fun a : SPACETMInstance => 6 * (2 * descLen a.machine + 5) * a.space)
      encSPACETMInstance encUnary :=
    ComputableInPolyTime.unary_mul'
      (ComputableInPolyTime.unary_mul' (.const 6) h2m5) hspace
  exact ComputableInPolyTime.unary_add' (ComputableInPolyTime.unary_add' hterm1 hterm2) (.const 6)

/-- Instance `a` accepts at step `t` when `budgetedUniversal` on `(a.machine, a.input.map eBit, t,
a.cfgBudget)` has halted with output `[eBit true]`. -/
def Accepts (a : SPACETMInstance) (t : ℕ) : Prop :=
  budgetedUniversal (a.machine, a.input.map eBit, t, a.cfgBudget) = ([eBit true], true)

instance (a : SPACETMInstance) (t : ℕ) : Decidable (a.Accepts t) :=
  inferInstanceAs (Decidable
    (budgetedUniversal (a.machine, a.input.map eBit, t, a.cfgBudget) = ([eBit true], true)))

private theorem eq_singleton_true_of_take_two_map_eBit {out : List Bool}
    (h : (out.map eBit).take 2 = [eBit true]) : out = [true] := by
  rcases out with _ | ⟨b, _ | ⟨b₂, rest⟩⟩
  · simp at h
  · simp only [List.map_cons, List.map_nil, List.take_succ_cons, List.take_nil,
      List.cons.injEq, and_true] at h
    exact congrArg (· :: []) (eBit.injective h)
  · simp at h

/-- On the description of a binary multi-tape machine `tm` whose run up to step `t` visits at most
`n` work-tape cells, `Accepts ⟨desc eS eBit tm, x, n⟩ t` holds if and only if `tm` has halted on `x`
by step `t` with output `[true]`. -/
theorem accepts_desc_iff_of_simSpace_le {k : ℕ} {State : Type} [Fintype State] (eS : State ↪ ℕ)
    (tm : MultiTapeTM k Bool State) (x : List Bool) (n t : ℕ)
    (hsp : simSpace (desc eS eBit tm) (x.map eBit) t ≤ n) :
    Accepts ⟨desc eS eBit tm, x, n⟩ t ↔
      (tm.runFrom (tm.initCfg x) t).Halted ∧
        (tm.runFrom (tm.initCfg x) t).output = [true] := by
  have hbud : cfgSpace (desc eS eBit tm) (x.map eBit) t ≤
      (⟨desc eS eBit tm, x, n⟩ : SPACETMInstance).cfgBudget :=
    cfgSpace_le_cfgBudget ⟨desc eS eBit tm, x, n⟩ hsp
  unfold Accepts
  rw [budgetedUniversal_desc eS eBit tm x t _ hbud, Prod.mk.injEq]
  refine ⟨fun ⟨hout, hhalt⟩ =>
      ⟨Option.isNone_iff_eq_none.mp hhalt, eq_singleton_true_of_take_two_map_eBit hout⟩,
    fun ⟨hhalt, hout⟩ => ⟨by rw [hout]; rfl, Option.isNone_iff_eq_none.mpr hhalt⟩⟩

/-- Clocked Boolean decider for `SPACETM`: run `budgetedUniversal` for `2 ^ (a.cfgBudget + 1)`
steps within configuration budget `a.cfgBudget` and test whether the result is
`([eBit true], true)`. -/
def decider (a : SPACETMInstance) : Bool :=
  decide (budgetedUniversal (a.machine, a.input.map eBit, 2 ^ (a.cfgBudget + 1),
    a.cfgBudget) = ([eBit true], true))

/-- The clocked decider `SPACETMInstance.decider` is computable in polynomial space. -/
theorem computableInPolySpace_decider :
    ComputableInPolySpace decider encSPACETMInstance encBool := by
  have hinput : ComputableInPolyTime
      (fun a : SPACETMInstance =>
        (a.machine, a.input.map eBit, 2 ^ (a.cfgBudget + 1), a.cfgBudget))
      encSPACETMInstance eInS := by
    have hmap : ComputableInPolyTime (fun a : SPACETMInstance => a.input.map eBit)
        encSPACETMInstance (encList encUnary) :=
      computableInPolyTime_map_eBit.comp (encSPACETMInstance_input_polyTime .id')
    have hclock : ComputableInPolyTime (fun a : SPACETMInstance => 2 ^ (a.cfgBudget + 1))
        encSPACETMInstance encNat :=
      ComputableInPolyTime.binary_two_pow.comp (by fun_prop)
    exact (encSPACETMInstance_machine_polyTime .id').prod
      (hmap.prod (hclock.prod computableInPolyTime_cfgBudget))
  have hverd : ComputableInPolyTime
      (fun r : List ℕ × Bool => decide (r = ([eBit true], true))) eOut encBool :=
    ComputableInPolyTime.decide_eq' .id' (.const _)
  exact (ComputableInPolySpace.of_polyTime hverd).comp
    (computableInPolySpace_budgetedUniversal.comp (ComputableInPolySpace.of_polyTime hinput))

end SPACETMInstance

/-- **Canonical space-bounded Turing machine acceptance (`SPACETM`)**
[Arora and Barak, Chapter 4, display (2) and Exercise 4 §3][AroraBarak07]:
the instances `a : SPACETMInstance` for which the simulation of `a.machine` on `a.input` within
configuration budget `a.cfgBudget` halts with output `[eBit true]` at some step `t`. -/
def SPACETM : Set SPACETMInstance :=
  {a | ∃ t : ℕ, a.Accepts t}

namespace SPACETM

theorem mem_iff {a : SPACETMInstance} : a ∈ SPACETM ↔ ∃ t : ℕ, a.Accepts t :=
  Iff.rfl

/-- **`SPACETM` is equivalent to acceptance at the configuration-count clock
`2 ^ (a.cfgBudget + 1)`.** -/
theorem mem_iff_accepts_clock (a : SPACETMInstance) :
    a ∈ SPACETM ↔ a.Accepts (2 ^ (a.cfgBudget + 1)) :=
  exists_budgetedUniversal_eq_true_iff a.machine (a.input.map eBit) a.cfgBudget [eBit true] le_rfl

/-- **`SPACETM` is decided by `SPACETMInstance.decider`.** -/
theorem mem_iff_decider (a : SPACETMInstance) :
    a ∈ SPACETM ↔ a.decider = true := by
  rw [mem_iff_accepts_clock, SPACETMInstance.decider, decide_eq_true_eq, SPACETMInstance.Accepts]

/-- **On the description of a machine `tm` that visits at most `n` work-tape cells on `x`**
(`tm.RunsInSpace x n`), `⟨desc eS eBit tm, x, n⟩ ∈ SPACETM` holds if and only if `tm` halts on `x`
with output `[true]`. -/
theorem desc_mem_iff_of_runsInSpace {k : ℕ} {State : Type} [Fintype State] (eS : State ↪ ℕ)
    (tm : MultiTapeTM k Bool State) (x : List Bool) (n : ℕ) (hsp : tm.RunsInSpace x n) :
    ⟨desc eS eBit tm, x, n⟩ ∈ SPACETM ↔
      ∃ t, (tm.runFrom (tm.initCfg x) t).Halted ∧
        (tm.runFrom (tm.initCfg x) t).output = [true] := by
  rw [mem_iff]
  refine exists_congr fun t =>
    SPACETMInstance.accepts_desc_iff_of_simSpace_le eS tm x n t ?_
  rw [simSpace_desc]
  exact space_le_of_runsInSpace hsp t

/-- **`SPACETM` is in `PSPACE`** (`Arora–Barak Exercise 4 §3`, membership). -/
theorem mem_PSPACE : SPACETM ∈ PSPACE encSPACETMInstance :=
  ⟨SPACETMInstance.decider, SPACETMInstance.computableInPolySpace_decider, mem_iff_decider⟩

/-- **Space-bounded problems reduce to `SPACETM`.** Every problem decided within space
`c₁ * p |enc a| + c₂` for a polynomial-time unary function `p` reduces to `SPACETM` in polynomial
time via `a ↦ ⟨desc eS eBit tm, enc a, c₁ * p |enc a| + c₂⟩`. -/
theorem polyTimeReducible {α : Type} {enc : α ↪ List Bool} {A : Set α} {p : ℕ → ℕ}
    (hp : ComputableInPolyTime p encUnary encUnary) {c₁ c₂ : ℕ} {t : α → ℕ}
    (hA : DecidableInTimeAndSpace A enc t (fun a => c₁ * p (enc a).length + c₂)) :
    PolyTimeReducible enc encSPACETMInstance A SPACETM := by
  obtain ⟨g, ⟨k, State, hfin, tm, htm⟩, hg⟩ := decidableInTimeAndSpace_iff.mp hA
  have := Fintype.ofFinite State
  let eS : State ↪ ℕ := (Fintype.equivFin State).toEmbedding.trans Fin.valEmbedding
  refine ⟨fun a => ⟨desc eS eBit tm, enc a, c₁ * p (enc a).length + c₂⟩, ?_, fun a => ?_⟩
  · have henc : ComputableInPolyTime (fun a => enc a) enc encBits := .of_eq fun _ => rfl
    have hlen : ComputableInPolyTime (fun a => (enc a).length) enc encUnary :=
      ComputableInPolyTime.length_bits.comp henc
    have hp_a : ComputableInPolyTime (fun a => p (enc a).length) enc encUnary := hp.comp hlen
    fun_prop
  · rw [desc_mem_iff_of_runsInSpace eS tm (enc a) (c₁ * p (enc a).length + c₂) (htm a).2.2, hg]
    obtain ⟨hhalt, hout⟩ := (htm a).runFrom_of_le le_rfl
    change (tm.runFrom (tm.initCfg (enc a)) (t a)).output = [g a] at hout
    refine ⟨fun h => ⟨t a, hhalt, by rw [hout, h]⟩, fun ⟨t', hhalt', hout'⟩ => ?_⟩
    rcases le_total t' (t a) with hle | hle
    · have heq : (tm.runFrom (tm.initCfg (enc a)) (t a)).output =
          (tm.runFrom (tm.initCfg (enc a)) t').output :=
        congrArg Cfg.output (MultiTapeTM.runFrom_eq_of_halt tm (tm.initCfg (enc a)) hle hhalt')
      rw [hout, hout'] at heq
      exact List.cons.inj heq |>.1
    · have heq : (tm.runFrom (tm.initCfg (enc a)) t').output =
          (tm.runFrom (tm.initCfg (enc a)) (t a)).output :=
        congrArg Cfg.output (MultiTapeTM.runFrom_eq_of_halt tm (tm.initCfg (enc a)) hle hhalt)
      rw [hout', hout] at heq
      exact List.cons.inj heq |>.1.symm

/-- **`SPACETM` is `PSPACE`-hard** under polynomial-time many-one reductions, quantifying over every
source type `α` and encoding `enc : α ↪ List Bool` (`Arora–Barak Exercise 4 §3`, hardness). -/
theorem pspaceHard : PSPACEHard encSPACETMInstance SPACETM := by
  intro α enc A hA
  obtain ⟨k, hk⟩ := mem_PSPACE_iff_exists_mem_DSPACE.mp hA
  obtain ⟨c₁, c₂, t, hdec⟩ := hk
  exact polyTimeReducible (p := fun n => n ^ k) (.of_tidy (.unary_pow k)) hdec

/-- **`SPACETM` is `PSPACE`-complete** under polynomial-time many-one reductions
(`Arora–Barak Exercise 4 §3`). -/
theorem pspaceComplete : PSPACEComplete encSPACETMInstance SPACETM :=
  ⟨mem_PSPACE, pspaceHard⟩

end SPACETM

end Cslib.Complexity
