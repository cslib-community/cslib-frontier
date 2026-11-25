/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (local addition beside the vendored `Turing.MultiTapeTM.Universal` files)

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.PolyTime
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Halting.Computable
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option

/-!
# Clocked runs of Boolean and word-output machines

`Turing.MultiTapeTM.Universal.runBool d w t` runs the machine described by `d` on the bit word `w`
for `t` steps with the universal function, and returns the bit it has output if it has halted
with a single bit, and `none` otherwise. `Turing.MultiTapeTM.Universal.runWord d w t` is the
word-output analogue: if the machine halts within `t` steps, it decodes the emitted symbol numbers
to bits via `(· != 0)` and returns `some o`, and `none` otherwise. With the number of steps in
unary, both are polynomial-time (`Turing.MultiTapeTM.Universal.computableInPolyTime_runBool`,
`Turing.MultiTapeTM.Universal.computableInPolyTime_runWord`).

Every computable Boolean function has a description whose clocked runs are sound and eventually
complete (`Turing.MultiTapeTM.IsComputable.exists_runBool`): a run never returns a wrong bit, and
returns the right one once it is allowed enough steps. Delayed diagonalization uses this to
compare computable sets on short words within a polynomial time budget, without knowing how long
the machines take, while Levin's universal search uses `runWord` to collect candidate witnesses.

## Main definitions

* `Turing.MultiTapeTM.Universal.runBool`: the bit output by a described machine within a number
  of steps, if any.
* `Turing.MultiTapeTM.Universal.runWord`: the bit word output by a described machine within a
  number of steps, if it halts.

## Main results

* `Turing.MultiTapeTM.Universal.runBool_eq_some_iff`: `runBool` through the universal function.
* `Turing.MultiTapeTM.Universal.computableInPolyTime_runBool`: `runBool` is polynomial-time with
  the number of steps in unary.
* `Turing.MultiTapeTM.Universal.runWord_eq_some_iff`, `Turing.MultiTapeTM.Universal.runWord_mono`,
  `Turing.MultiTapeTM.Universal.length_le_of_runWord_eq_some`,
  `Turing.MultiTapeTM.Universal.runWord_desc`,
  `Turing.MultiTapeTM.Universal.runWord_desc_of_halted`: semantics, monotonicity, and output-length
  bound of `runWord`.
* `Turing.MultiTapeTM.Universal.computableInPolyTime_runWord`: `runWord` is polynomial-time with
  the number of steps in unary.
* `Turing.MultiTapeTM.IsComputable.exists_runBool`: clocked runs of a computable Boolean function
  are sound and eventually complete.
-/

@[expose] public section

namespace Turing.MultiTapeTM

namespace Universal

/-- The bit output by the machine described by `d` on the bit word `w` within `t` steps: `some b`
if it has halted with output `[b]`, `none` otherwise. -/
def runBool (d : Desc) (w : List Bool) (t : ℕ) : Option Bool :=
  if universal (d, w.map eBit, t) = ([eBit true], true) then some true
  else if universal (d, w.map eBit, t) = ([eBit false], true) then some false
  else none

theorem runBool_eq_some_iff {d : Desc} {w : List Bool} {t : ℕ} {b : Bool} :
    runBool d w t = some b ↔ universal (d, w.map eBit, t) = ([eBit b], true) := by
  unfold runBool
  cases b <;> split_ifs with h₁ h₂ <;> simp_all [eBit]

/-- **Clocked runs are polynomial-time** with the number of steps in unary. -/
@[fun_prop]
theorem computableInPolyTime_runBool {α : Type} {input : α ↪ List Bool}
    {d : α → Desc} {w : α → List Bool} {t : α → ℕ}
    (hd : ComputableInPolyTime d input eDesc) (hw : ComputableInPolyTime w input encBits)
    (ht : ComputableInPolyTime t input encUnary) :
    ComputableInPolyTime (fun a => runBool (d a) (w a) (t a)) input (encOption encBool) := by
  unfold runBool
  fun_prop

/-- The bit word output by the machine described by `d` on the bit word `w` within `t` steps:
`some o` if it has halted, with its emitted symbol numbers decoded via `(· != 0)`, and `none`
otherwise. -/
def runWord (d : Desc) (w : List Bool) (t : ℕ) : Option (List Bool) :=
  let r := universal (d, w.map eBit, t)
  if r.2 then some (r.1.map (· != 0)) else none

theorem runWord_eq_some_iff {d : Desc} {w o : List Bool} {t : ℕ} :
    runWord d w t = some o ↔
      ∃ u, universal (d, w.map eBit, t) = (u, true) ∧ u.map (· != 0) = o := by
  unfold runWord
  rcases h : universal (d, w.map eBit, t) with ⟨u, _ | _⟩ <;> simp [eq_comm]

/-- Once a described machine halts, giving it more steps preserves its output word. -/
theorem runWord_mono {d : Desc} {w o : List Bool} {t₁ t₂ : ℕ} (ht : t₁ ≤ t₂)
    (h : runWord d w t₁ = some o) : runWord d w t₂ = some o := by
  obtain ⟨u, hu, rfl⟩ := runWord_eq_some_iff.mp h
  refine runWord_eq_some_iff.mpr ⟨u, ?_, rfl⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ht
  simp only [universal, simulate] at hu ⊢
  rcases hiter : (stepOut d (w.map eBit))^[t₁] (init d, []) with ⟨c, out⟩
  rw [hiter] at hu
  simp only [Prod.mk.injEq, Option.isNone_iff_eq_none] at hu
  rcases hu with ⟨rfl, hstate⟩
  rw [Nat.add_comm, Function.iterate_add_apply, hiter,
    Function.iterate_fixed (stepOut_of_state_eq_none hstate out)]
  simp [hstate]

/-- A machine halted within `t` steps emits a word of length at most `t`. -/
theorem length_le_of_runWord_eq_some {d : Desc} {w o : List Bool} {t : ℕ}
    (h : runWord d w t = some o) : o.length ≤ t := by
  obtain ⟨u, hu, rfl⟩ := runWord_eq_some_iff.mp h
  obtain ⟨_, hlen, _⟩ := inv_iterate d (w.map eBit) t
  have hu' : ((stepOut d (w.map eBit))^[t] (init d, [])).2 = u := congrArg Prod.fst hu
  simpa [hu'] using hlen

/-- On the description of a finite binary machine, `runWord` returns its output iff the machine has
halted within `t` steps. -/
theorem runWord_desc {k : ℕ} {State : Type} [Fintype State] (eS : State ↪ ℕ)
    (tm : MultiTapeTM k Bool State) (w : List Bool) (t : ℕ) :
    runWord (desc eS eBit tm) w t =
      if (tm.runFrom (tm.initCfg w) t).Halted then
        some (tm.runFrom (tm.initCfg w) t).output
      else none := by
  unfold runWord
  rw [universal_desc]
  simp only [Cfg.Halted]
  cases (tm.runFrom (tm.initCfg w) t).state with
  | none =>
    simp only [Option.isNone_none, ↓reduceIte, Option.some.injEq, List.map_map]
    have hbit : ((· != 0) ∘ eBit) = id := by
      funext b
      cases b <;> rfl
    simp [hbit]
  | some _ => simp

/-- If a finite binary machine halts within `t` steps on `w`, then `runWord` on its description for
any `T ≥ t` steps returns its output. -/
theorem runWord_desc_of_halted {k : ℕ} {State : Type} [Fintype State] (eS : State ↪ ℕ)
    (tm : MultiTapeTM k Bool State) {w : List Bool} {t T : ℕ}
    (hhalt : (tm.runFrom (tm.initCfg w) t).Halted) (hT : t ≤ T) :
    runWord (desc eS eBit tm) w T = some (tm.runFrom (tm.initCfg w) t).output := by
  rw [runWord_desc, runFrom_eq_of_halt tm _ hT hhalt, ite_eq_left hhalt]

/-- **Clocked word-output runs are polynomial-time** with the number of steps in unary. -/
@[fun_prop]
theorem computableInPolyTime_runWord {α : Type} {input : α ↪ List Bool}
    {d : α → Desc} {w : α → List Bool} {t : α → ℕ}
    (hd : ComputableInPolyTime d input eDesc) (hw : ComputableInPolyTime w input encBits)
    (ht : ComputableInPolyTime t input encUnary) :
    ComputableInPolyTime (fun a => runWord (d a) (w a) (t a)) input (encOption encBits) := by
  unfold runWord
  have hsim : ComputableInPolyTime (fun a => universal (d a, (w a).map eBit, t a)) input eOut :=
    computableInPolyTime_universal.comp
      (hd.prod ((computableInPolyTime_map_eBit.comp hw).prod ht))
  have h1 : ComputableInPolyTime (fun a => (universal (d a, (w a).map eBit, t a)).1) input
      (encList encUnary) :=
    (ComputableInPolyTime.fst (encList encUnary) encBool).comp hsim
  have h2 : ComputableInPolyTime (fun a => (universal (d a, (w a).map eBit, t a)).2) input
      encBool :=
    (ComputableInPolyTime.snd (encList encUnary) encBool).comp hsim
  have hout : ComputableInPolyTime
      (fun a => some ((universal (d a, (w a).map eBit, t a)).1.map (· != 0))) input
      (encOption encBits) :=
    (ComputableInPolyTime.optionSome encBits).comp (computableInPolyTime_map_ne_zero.comp h1)
  exact ComputableInPolyTime.ite' h2 hout (ComputableInPolyTime.const none)

end Universal

open Universal

/-- **Clocked runs of a computable Boolean function.** A computable `f` has a description whose
clocked runs never return a wrong bit and return the right one from some number of steps on. -/
theorem IsComputable.exists_runBool {α : Type} {enc : α ↪ List Bool} {f : α → Bool}
    (hf : IsComputable f enc encBool) :
    ∃ d : Desc, (∀ a t b, runBool d (enc a) t = some b → b = f a) ∧
      ∀ a, ∃ T, ∀ t, T ≤ t → runBool d (enc a) t = some (f a) := by
  obtain ⟨k, State, hfin, tm, htm⟩ := isComputable_iff.mp hf
  have := Fintype.ofFinite State
  let eS : State ↪ ℕ := (Fintype.equivFin State).toEmbedding.trans Fin.valEmbedding
  refine ⟨desc eS eBit tm, fun a t b hb => ?_, fun a => ?_⟩
  · obtain ⟨u, hhalt, hout⟩ := htm a
    rw [runBool_eq_some_iff, universal_desc, Prod.mk.injEq, Option.isNone_iff_eq_none] at hb
    obtain ⟨hb, ht⟩ := hb
    -- the runs for `t` and `u` steps have both halted, so they agree
    have heq : tm.runFrom (tm.initCfg (enc a)) t = tm.runFrom (tm.initCfg (enc a)) u := by
      rcases le_total t u with h | h
      · exact (runFrom_eq_of_halt tm _ h ht).symm
      · exact runFrom_eq_of_halt tm _ h hhalt
    rw [heq, hout] at hb
    exact (eBit.injective (List.singleton_injective hb)).symm
  · -- past its halting time, the machine has halted with output `[f a]`
    obtain ⟨u, hhalt, hout⟩ := htm a
    refine ⟨u, fun t ht => runBool_eq_some_iff.mpr ?_⟩
    rw [universal_desc, runFrom_eq_of_halt tm _ ht hhalt, hout, hhalt]
    rfl

end Turing.MultiTapeTM
