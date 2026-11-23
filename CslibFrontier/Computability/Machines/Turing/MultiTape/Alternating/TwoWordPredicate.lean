/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.TwoWordInput
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.WorkTapePredicate
import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.AppendWord
import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.RewindWork
import Mathlib.Tactic.FinCases

/-!
# Native predicates on two stored words

Two raw words on distinct work tapes are serialized once into the standard pair encoding.
The first word is framed, the second is appended without framing, and the destination is rewound
before the native predicate runs. The input-dependent predicate clock is retained: serialization
adds a linear term, rather than replacing the clock by a polynomial in the complete pair length.

## Main results

* `Turing.MultiTapeATM.TwoWordPredicate.exists_of_inO`: one finite alternating leaf evaluates a
  Boolean predicate from two stored words, charging both serialization and native execution.
-/

public section

namespace Turing.MultiTapeATM.TwoWordPredicate

open MultiTapeTM

private def fields (x y : List Bool) : Fin 2 → List Bool := ![x, y]

private def prefixWord (x y : List Bool) : Fin 3 → List Bool :=
  ![[], frame x, frame x ++ y]

private def phaseTapes (i : Fin 2) : Fin 2 ↪ Fin 3 where
  toFun := ![i.castSucc, 2]
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;> try rfl
    all_goals have hi := i.isLt; have hv := congrArg Fin.val h; simp at hv; omega

@[simp] private theorem phaseTapes_source (i : Fin 2) : phaseTapes i 0 = i.castSucc := rfl

@[simp] private theorem phaseTapes_dest (i : Fin 2) : phaseTapes i 1 = Fin.last 2 := rfl

private noncomputable def phase (i : Fin 2) :=
  (AppendWord.machine (decide (i.val = 0))).extendTapes (phaseTapes i)

private def stage (input x y : List Bool) (n : Fin 3) : Cfg 3 Bool Unit input :=
  tapesCfg input (Fin.lastCases (prefixWord x y n) (fields x y)) 0
    (Fin.lastCases ((prefixWord x y n).length : ℤ)
      (fun i => if i.val < n.val then ((fields x y i).length : ℤ) else 0)) []

private theorem prefix_next (x y : List Bool) (i : Fin 2) :
    prefixWord x y i.succ = prefixWord x y i.castSucc ++
      AppendWord.fragment (decide (i.val = 0)) (fields x y i) := by
  fin_cases i <;> simp [prefixWord, fields, AppendWord.fragment]

private theorem runs_phase (input x y : List Bool) (i : Fin 2) :
    RunsBetween (phase i) (stage input x y i.castSucc) (stage input x y i.succ)
      (AppendWord.clock (decide (i.val = 0)) (fields x y i))
      (2 * (AppendWord.clock (decide (i.val = 0)) (fields x y i) + 1) + 1) := by
  have hv : viewCfg (phaseTapes i) (stage input x y i.castSucc) =
      AppendWord.config input (fields x y i) (prefixWord x y i.castSucc) 0 [] := by
    apply Cfg.ext <;> try rfl
    all_goals
      funext j
      fin_cases j <;>
        simp only [viewCfg, stage, tapesCfg, Nat.reduceAdd, Pi.zero_apply, sub_zero,
          Fin.val_castSucc, Fin.val_fin_lt, Fin.zero_eta, Fin.isValue, phaseTapes_source,
          Fin.lastCases_castSucc, AppendWord.config, CharP.cast_eq_zero, Matrix.cons_val_zero,
          Fin.mk_one, phaseTapes_dest, Fin.reduceLast, Matrix.cons_val_one,
          Matrix.cons_val_fin_one, lt_self_iff_false, ↓reduceIte]
    all_goals rw [show (2 : Fin 3) = Fin.last 2 from rfl, Fin.lastCases_last]
  have h := AppendWord.runsBetween (decide (i.val = 0)) input (fields x y i)
    (prefixWord x y i.castSucc) []
  rw [← hv] at h
  have he := h.extendTapes (phaseTapes i)
  have heq : embed (phaseTapes i)
      (AppendWord.config input (fields x y i)
        (prefixWord x y i.castSucc ++ AppendWord.fragment (decide (i.val = 0)) (fields x y i))
        (fields x y i).length [])
      (stage input x y i.castSucc).workTapes (stage input x y i.castSucc).workTapePos =
        stage input x y i.succ := by
    apply embed_tapesCfg
    · intro j
      fin_cases j <;>
        simp only [Nat.reduceAdd, prefix_next, Fin.val_eq_zero_iff, Fin.isValue, Fin.zero_eta,
          phaseTapes_source, Fin.lastCases_castSucc, Matrix.cons_val_zero, Pi.zero_apply,
          List.length_append, Nat.cast_add, Fin.val_succ, Order.lt_add_one_iff, Fin.val_fin_le,
          Std.le_refl, ↓reduceIte, and_self, Fin.mk_one, phaseTapes_dest, Fin.reduceLast,
          Matrix.cons_val_one, Matrix.cons_val_fin_one, true_and]
      constructor <;> rw [show (2 : Fin 3) = Fin.last 2 from rfl, Fin.lastCases_last]
    · intro j hj
      cases j using Fin.lastCases with
      | last => exact (hj ⟨1, rfl⟩).elim
      | cast j =>
        have hne : j ≠ i := by
          intro hji
          subst j
          exact hj ⟨0, rfl⟩
        have hv : j.val ≠ i.val := fun h => hne (Fin.ext h)
        simp only [Fin.lastCases_castSucc, Pi.zero_apply, Fin.val_castSucc,
          Fin.val_succ, true_and]
        split_ifs <;> (first | rfl | omega)
  rw [heq] at he
  exact he

private def finished (input x y : List Bool) : Cfg 3 Bool Unit input :=
  tapesCfg input (Fin.lastCases (frame x ++ y) (fields x y)) 0
    (Fin.lastCases 0 (fun i => ((fields x y i).length : ℤ))) []

private noncomputable def rewind :=
  (rewindWork Bool).extendTapes (tapeEmb (Fin.last 2))

private theorem runs_rewind (input x y : List Bool) :
    RunsBetween rewind (stage input x y 2) (finished input x y)
      ((frame x ++ y).length + 2) (3 * ((frame x ++ y).length + 3)) := by
  apply RunsBetween.of_runFrom
  simp only [rewind, runFrom_tapeEmb, oneTapeCfg, stage, tapesCfg, Cfg.withState,
    extendTapes_q₀, Pi.zero_apply, sub_zero, Fin.lastCases_last]
  rw [show prefixWord x y 2 = frame x ++ y from rfl,
    runFrom_rewindWork_none _ _ _ rfl le_rfl, embed_tapeEmb]
  apply Cfg.ext <;> try rfl
  all_goals
    funext j
    cases j using Fin.lastCases with
    | last =>
      simp only [Nat.reduceAdd, Fin.reduceLast, Function.update_self, finished, tapesCfg,
        Pi.zero_apply, sub_zero, Fin.isValue, List.length_append, length_frame, Nat.cast_add,
        Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, Fin.coe_ofNat_eq_mod, Nat.mod_succ,
        Order.lt_two_iff]
      rw [show (2 : Fin 3) = Fin.last 2 from rfl, Fin.lastCases_last]
    | cast j =>
      have hn : j.castSucc ≠ (2 : Fin 3) := Fin.castSucc_ne_last j
      have hj : j.val ≤ 1 := by omega
      simp [finished, tapesCfg, hn, hj]

private noncomputable def serialize := ((phase 0).seq ((phase 1).seq rewind)).fromLeftBlank

private theorem runs_serialize (input x y : List Bool) :
    RunsBetween (input := input) serialize { stage input x y 0 with inputPos := 0 }
      { finished input x y with inputPos := 0 }
      (2 * (frame x ++ y).length + 5) (5 * (frame x ++ y).length + 29) := by
  have h := ((runs_phase input x y 0).seq
    ((runs_phase input x y 1).seq (runs_rewind input x y))).fromLeftBlank rfl rfl
  convert h using 1 <;> (first | rfl | (simp [AppendWord.clock, fields]; omega))

private def serializeTapes (k : ℕ) : Fin 3 ↪ Fin (2 + (k + 2)) where
  toFun := ![(0 : Fin 2).castAdd (k + 2), (1 : Fin 2).castAdd (k + 2),
    Fin.natAdd 2 (Fin.natAdd k 0)]
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;> try rfl
    all_goals have hv := congrArg Fin.val h; dsimp at hv; omega

/-- A native predicate on a pair can start with its two components on separate work tapes.
The same finite alternating machine works for every pair and every host input. Framing, copying,
rewinding and the normalized predicate computation all appear in the common linear-plus-`T`
clock; the separate space certificate is used only by the native predicate normalization. -/
theorem exists_of_inO {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {f : α × β → Bool} {T W : α × β → ℕ}
    (hf : ComputableInO f (encPair encA encB) encBool T W) :
    ∃ (K : ℕ) (i j : Fin K) (Q : Type) (_ : Finite Q) (atm : MultiTapeATM K Bool Q) (c : ℕ),
      i ≠ j ∧ ∀ (input : List Bool) (a : α) (b : β),
        let cfg := (TwoWordInput.ready i j input (encA a) (encB b)).withState
          (some atm.toPTM.initial)
        let time := c * ((encPair encA encB (a, b)).length + T (a, b) + 1)
        atm.HaltsWithin time cfg ∧ (atm.AcceptsWithin time cfg ↔ f (a, b) = true) := by
  obtain ⟨k, S, hS, runner, c, hr⟩ := WorkTapePredicate.exists_of_inO hf
  let i : Fin (2 + (k + 2)) := (0 : Fin 2).castAdd (k + 2)
  let j : Fin (2 + (k + 2)) := (1 : Fin 2).castAdd (k + 2)
  let E := serializeTapes k
  let B : Fin (k + 2) ↪ Fin (2 + (k + 2)) := Fin.natAddEmb 2
  let prep := serialize.extendTapes E
  let sub := runner.extendTapes B
  let tm := prep.seq sub
  let atm := MultiTapeATM.ofTMs (fun _ => tm) (fun _ => false)
  refine ⟨_, i, j, _, inferInstance, atm, c + 5, ?_, ?_⟩
  · intro h
    have hv := congrArg Fin.val h
    simp [i, j] at hv
  intro input a b
  dsimp only
  let start := TwoWordInput.ready i j input (encA a) (encB b)
  let finish : Cfg (2 + (k + 2)) Bool Unit input :=
    embed E { finished input (encA a) (encB b) with inputPos := 0 }
    start.workTapes start.workTapePos
  have he (l : Fin 3) : E l = ![i, j, B (Fin.natAdd k 0)] l := rfl
  have hv : viewCfg E start = { stage input (encA a) (encB b) 0 with inputPos := 0 } := by
    apply Cfg.ext <;> try rfl
    · funext l z
      simp only [viewCfg, start, TwoWordInput.ready, wordsCfg, stage, tapesCfg,
        Pi.zero_apply, sub_zero]
      cases l using Fin.lastCases with
      | last =>
        rw [Fin.lastCases_last]
        simp [TwoWordInput.words, he, B, i, j, prefixWord,
          (Fin.castAdd_ne_natAdd _ _).symm]
      | cast l =>
        rw [Fin.lastCases_castSucc]
        fin_cases l <;> simp [TwoWordInput.words, he, i, j, fields]
    · funext l
      simp only [viewCfg, start, TwoWordInput.ready, wordsCfg, stage, tapesCfg]
      cases l using Fin.lastCases with
      | last => rw [Fin.lastCases_last]; rfl
      | cast l =>
        rw [Fin.lastCases_castSucc]
        simp
  have hprep := runs_serialize input (encA a) (encB b)
  rw [← hv] at hprep
  have hprep' := hprep.extendTapes E
  have hnot (l : Fin (k + 2)) (hl : l ≠ Fin.natAdd k 0) : B l ∉ Set.range E := by
    rintro ⟨m, hm⟩
    fin_cases m
    · exact Fin.castAdd_ne_natAdd _ _ hm
    · exact Fin.castAdd_ne_natAdd _ _ hm
    · exact hl (B.injective hm).symm
  have hview : viewCfg B finish = WorkTapePredicate.config input (encPair encA encB (a, b)) := by
    apply Cfg.ext <;> try rfl
    · funext l
      by_cases hl : l = Fin.natAdd k 0
      · subst l
        change finish.workTapes (E 2) = _
        dsimp only [finish]
        rw [embed_workTapes_embed]
        simp only [finished, tapesCfg, Nat.reduceAdd, Pi.zero_apply, sub_zero, Fin.isValue,
          WorkTapePredicate.config, encPair_apply, Function.update_self]
        rw [show (2 : Fin 3) = Fin.last 2 from rfl, Fin.lastCases_last]
      · change finish.workTapes (B l) = _
        dsimp only [finish]
        rw [embed_workTapes_of_notMem_range _ _ _ _ (hnot l hl)]
        simp [start, TwoWordInput.ready, TwoWordInput.words, wordsCfg,
          WorkTapePredicate.config, tapesCfg, B, i, j, hl,
          (Fin.castAdd_ne_natAdd _ _).symm]
    · funext l
      by_cases hl : l = Fin.natAdd k 0
      · subst l
        change finish.workTapePos (E 2) = _
        dsimp only [finish]
        rw [embed_workTapePos_embed]
        simp only [finished, tapesCfg, Nat.reduceAdd, Pi.zero_apply, sub_zero, Fin.isValue,
          WorkTapePredicate.config, encPair_apply]
        rw [show (2 : Fin 3) = Fin.last 2 from rfl, Fin.lastCases_last]
      · change finish.workTapePos (B l) = _
        dsimp only [finish]
        rw [embed_workTapePos_of_notMem_range _ _ _ _ (hnot l hl)]
        rfl
  let result := embed B (WorkTapePredicate.config input (encPair encA encB (a, b)) [f (a, b)])
    finish.workTapes finish.workTapePos
  have hsub : sub.runFrom (finish.withState (some sub.q₀)) (c * (T (a, b) + 1)) =
      result.withState none := by
    rw [show sub = runner.extendTapes B from rfl, runFrom_extendTapes]
    have hv' := congrArg (fun q => q.withState (some runner.q₀)) hview
    change viewCfg B (finish.withState (some runner.q₀)) =
      (WorkTapePredicate.config input (encPair encA encB (a, b))).withState
        (some runner.q₀) at hv'
    rw [extendTapes_q₀, hv', hr]
    rfl
  have hall : tm.runFrom (start.withState (some tm.q₀))
      (2 * (encPair encA encB (a, b)).length + 5 + c * (T (a, b) + 1)) =
        result.withState none := by
    have hp : prep.runFrom (start.withState (some prep.q₀))
        (2 * (encPair encA encB (a, b)).length + 5) = finish.withState none := by
      simpa only [encPair_apply] using hprep'.1
    exact runFrom_seq hp rfl hsub rfl
  have hbound : 2 * (encPair encA encB (a, b)).length + 5 + c * (T (a, b) + 1) ≤
      (c + 5) * ((encPair encA encB (a, b)).length + T (a, b) + 1) := by
    nlinarith
  have hrun : tm.runFrom (start.withState (some tm.q₀))
      ((c + 5) * ((encPair encA encB (a, b)).length + T (a, b) + 1)) =
        result.withState none := by
    rw [runFrom_eq_of_halt _ _ hbound (by rw [hall]; rfl), hall]
  constructor
  · rw [haltsWithin_ofTMs_const_iff]
    change (tm.runFrom (start.withState (some tm.q₀)) _).state = none
    rw [hrun]
    rfl
  · rw [acceptsWithin_ofTMs_const_iff]
    change (tm.runFrom (start.withState (some tm.q₀)) _).state = none ∧
      (tm.runFrom (start.withState (some tm.q₀)) _).output = [true] ↔ _
    rw [hrun]
    simp [result, WorkTapePredicate.config, tapesCfg, Cfg.withState]

end Turing.MultiTapeATM.TwoWordPredicate
