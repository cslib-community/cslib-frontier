/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.ForwardWork
import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.RewindWork
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.DecoderPrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.KernelOnWords
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NormalForm
import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.Cursor
import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.ExtendTapes
import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.InputFromTape
import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.ReadInput
import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.Sequential
import CslibFrontier.Computability.Machines.Turing.MultiTape.Tactic.Step

/-!
# Evaluating functions that depend only on a bounded suffix prefix

If `f : α × List Bool → β` is computable in polynomial time on `encPair encA encBits`,
`cap : α → ℕ` is unary polynomial-time on `encA`, and `f (a, raw) = f (a, raw.take (cap a + 1))`
for all `a` and `raw`, then `f` is computed by a single deterministic multi-tape Turing machine
whose worst-case time and space on `(a, raw)` are bounded by polynomials in `(encA a).length`
alone, completely independent of `raw.length`.

This eliminates arbitrary raw-input length dependence for bounded-length verifiers (for example,
cryptographic verifiers that reject oversized prover strings before parsing them).
-/

namespace Turing.MultiTapeTM

open Cslib

section Helpers

/-- Reads one binary `frame` from the input tape, echoing the raw framed bits verbatim and halting
on its terminating `false` marker. -/
private def frameStopReader : InputReader Bool Bool where
  q₀ := false
  step
    | false, true => (some true, some true)
    | false, false => (none, some false)
    | true, bit => (some false, some bit)

private lemma read_frameStopReader (word rest : List Bool) :
    frameStopReader.read false (frame word ++ rest) = (frame word, (frame word).length) := by
  induction word with
  | nil => rfl
  | cons bit word ih =>
    rw [frame_cons, List.cons_append, List.cons_append,
      frameStopReader.read_cons_of_some (q' := true) _ rfl,
      frameStopReader.read_cons_of_some (q' := false) _ rfl, ih]
    simp [frameStopReader, Nat.add_assoc]

/-- Two-tape machine starting with the input cursor on `raw`, tape `0` holding `encUnary N` at
position `0`, and tape `1` at the frontier of `u₀`. It copies `raw.take N` after `u₀` on tape `1`
and halts after `min N raw.length + 1` steps. -/
private def copyCappedCore : MultiTapeTM 2 Bool Unit :=
  ofTr () fun _ inp work =>
    match work 0, inp with
    | some _, some b => ⟨1, ![(none, 1), (some (some b), 1)], none, some ()⟩
    | _, _ => ⟨0, fun _ => (none, 0), none, none⟩

private lemma copyCappedCore_runFrom_walk
    {u₀ raw out : List Bool} {N : ℕ} (m : ℕ) (hm : m ≤ min N raw.length) :
    copyCappedCore.runFrom (input := u₀ ++ raw)
      ⟨some (), ⟨1 + u₀.length, by rw [List.length_append]; omega⟩,
        ![tapeOfList (List.replicate N true), tapeOfList u₀],
        ![0, (u₀.length : ℤ)], out⟩ m =
      ⟨some (), ⟨1 + u₀.length + m, by rw [List.length_append]; omega⟩,
        ![tapeOfList (List.replicate N true), tapeOfList (u₀ ++ raw.take m)],
        ![(m : ℤ), ((u₀.length + m : ℕ) : ℤ)], out⟩ := by
  induction m with
  | zero => simp [runFrom]
  | succ m ih =>
    have hltN : m < N := by omega
    have hltRaw : m < raw.length := by omega
    have hlen : (u₀ ++ raw.take m).length = u₀.length + m := by
      simp [List.length_take, Nat.min_eq_left hltRaw.le]
    rw [runFrom, Function.iterate_succ_apply', ← runFrom, ih (by omega), step_of_state rfl]
    let cur : Cfg 2 Bool Unit (u₀ ++ raw) :=
      ⟨some (), ⟨1 + u₀.length + m, by rw [List.length_append]; omega⟩,
        ![tapeOfList (List.replicate N true), tapeOfList (u₀ ++ raw.take m)],
        ![(m : ℤ), ((u₀.length + m : ℕ) : ℤ)], out⟩
    have hinp : cur.inputSymbol = some raw[m] := by
      rw [inputSymbolInner (cfg := cur) (u₀.length + m) (by simp [cur, Nat.add_assoc])
        (by rw [List.length_append]; omega)]
      simp [List.getElem_append_right]
    have hwork0 : (tapeOfList (List.replicate N true) (m : ℤ)) = some true := by
      simp [tapeOfList_ofNat, hltN]
    change (copyCappedCore.tr () cur.inputSymbol cur.workTapeSymbols).apply cur = _
    rw [copyCappedCore, tr_ofTr, hinp, show cur.workTapeSymbols 0 = some true from hwork0]
    refine Cfg.ext rfl (Fin.ext ?_) (funext fun i => ?_) (funext fun i => ?_) (by simp [cur])
    · have hlenApp : (u₀ ++ raw).length = u₀.length + raw.length := List.length_append
      have hinpPos : (↑(1 + u₀.length + m) + (1 : ℤ)).toNat = 1 + u₀.length + (m + 1) := by omega
      change (moveInputPos cur.inputPos 1).val = 1 + u₀.length + (m + 1)
      simp only [moveInputPos, cur, SignType.cast, hinpPos]
      split_ifs
      · rfl
      · dsimp; omega
    · fin_cases i
      · simp [cur, Action.apply]
      · change Function.update (tapeOfList (u₀ ++ raw.take m))
            ((u₀.length + m : ℕ) : ℤ) (some raw[m]) =
          tapeOfList (u₀ ++ raw.take (m + 1))
        rw [← hlen, ← tapeOfList_append_single, List.append_assoc,
          List.take_add_one, List.getElem?_eq_getElem hltRaw, Option.toList_some]
    · fin_cases i
      · simp [cur, Action.apply]
      · simp [cur, Action.apply]; omega

private lemma copyCappedCore_runFrom_halt
    {u₀ raw out : List Bool} {N : ℕ} :
    let m := min N raw.length
    copyCappedCore.runFrom (input := u₀ ++ raw)
      ⟨some (), ⟨1 + u₀.length, by rw [List.length_append]; omega⟩,
        ![tapeOfList (List.replicate N true), tapeOfList u₀],
        ![0, (u₀.length : ℤ)], out⟩ (m + 1) =
      ⟨none, ⟨1 + u₀.length + m, by rw [List.length_append]; omega⟩,
        ![tapeOfList (List.replicate N true), tapeOfList (u₀ ++ raw.take N)],
        ![(m : ℤ), ((u₀.length + m : ℕ) : ℤ)], out⟩ := by
  intro m
  have htake : raw.take m = raw.take N := by
    rcases le_total N raw.length with h | h <;> simp [m, h, List.take_of_length_le]
  rw [runFrom, Function.iterate_succ_apply', ← runFrom,
    copyCappedCore_runFrom_walk m le_rfl, step_of_state rfl]
  rcases min_cases N raw.length with ⟨hm, _⟩ | ⟨hm, _⟩
  · have hwork0 : tapeOfList (List.replicate N true) (m : ℤ) = none :=
      (tapeOfList_eq_none_iff _ _).mpr (Or.inr (by simp [m, hm]))
    simp only [copyCappedCore, tr_ofTr, Action.apply, Cfg.workTapeSymbols, Matrix.cons_val_zero,
      hwork0, htake]
    refine Cfg.ext rfl (Fin.ext (by simp)) ?_ ?_ (by simp) <;> funext i <;> fin_cases i <;> simp
  · have hinp : Cfg.inputSymbol (k := 2) (Symbol := Bool) (State := Unit) (input := u₀ ++ raw)
        ⟨some (), ⟨1 + u₀.length + m, by rw [List.length_append]; omega⟩,
          ![tapeOfList (List.replicate N true), tapeOfList (u₀ ++ raw.take m)],
          ![(m : ℤ), ((u₀.length + m : ℕ) : ℤ)], out⟩ = none :=
      inputSymbol_eq_none_of_boundary (Or.inr (by simp [m, hm]; omega))
    simp only [copyCappedCore, tr_ofTr]
    rcases hwork0 : tapeOfList (List.replicate N true) (m : ℤ) with _ | b <;>
      simp only [Action.apply, Cfg.workTapeSymbols, Matrix.cons_val_zero, hwork0, hinp] <;>
      refine Cfg.ext rfl (Fin.ext (by simp)) ?_ ?_ (by simp) <;>
      funext i <;> fin_cases i <;> simp [htake]

/-- Helper sequential rewind of tapes `1` and `0`. -/
private noncomputable def rewindBothTM :
    MultiTapeTM 2 Bool (RewindWorkState ⊕ RewindWorkState) :=
  ((rewindWork Bool).extendTapes (tapeEmb 1)).seq ((rewindWork Bool).extendTapes (tapeEmb 0))

/-- Composite 2-tape machine that advances tape `1` to the end of `u₀`, copies up to `N` bits
from the input cursor onto tape `1`, and rewinds both tape heads back to `0`. -/
private noncomputable def appendPrefixTM :
    MultiTapeTM 2 Bool ((Unit ⊕ Unit) ⊕ (RewindWorkState ⊕ RewindWorkState)) :=
  (((forwardWork Bool).extendTapes (tapeEmb 1)).seq copyCappedCore).seq rewindBothTM

private lemma transformsWordsAt_appendPrefixTM (u₀ raw : List Bool) (N : ℕ) :
    TransformsWordsAt appendPrefixTM (u₀ ++ raw)
      (1 + u₀.length) (1 + u₀.length + min N raw.length)
      ![List.replicate N true, u₀]
      ![List.replicate N true, u₀ ++ raw.take N]
      []
      ((u₀.length + 1) + (min N raw.length + 1) +
        ((u₀.length + min N raw.length + 2) + (min N raw.length + 2)))
      ((2 * (u₀.length + 1 + 1)) + (2 * (min N raw.length + 1 + 1)) +
        ((2 * (u₀.length + min N raw.length + 2 + 1)) + (2 * (min N raw.length + 2 + 1)))) := by
  rintro input p ws out ⟨rfl, hp, rfl⟩
  let p₀ : Fin ((u₀ ++ raw).length + 2) := ⟨1 + u₀.length, by rw [List.length_append]; omega⟩
  rw [show p = p₀ from Fin.ext hp]
  let pEnd : Fin ((u₀ ++ raw).length + 2) :=
    ⟨1 + u₀.length + min N raw.length, by rw [List.length_append]; omega⟩
  let cfg₀ : Cfg 2 Bool Unit (u₀ ++ raw) :=
    wordsCfgAt (u₀ ++ raw) p₀ (some ()) ![List.replicate N true, u₀] out
  let cfg₁ : Cfg 2 Bool Unit (u₀ ++ raw) :=
    ⟨none, p₀, ![tapeOfList (List.replicate N true), tapeOfList u₀], ![0, (u₀.length : ℤ)], out⟩
  let cfg₂ : Cfg 2 Bool Unit (u₀ ++ raw) :=
    ⟨none, pEnd, ![tapeOfList (List.replicate N true), tapeOfList (u₀ ++ raw.take N)],
      ![(min N raw.length : ℤ), ((u₀.length + min N raw.length : ℕ) : ℤ)], out⟩
  let cfg₃ : Cfg 2 Bool RewindWorkState (u₀ ++ raw) :=
    ⟨none, pEnd, ![tapeOfList (List.replicate N true), tapeOfList (u₀ ++ raw.take N)],
      ![(min N raw.length : ℤ), 0], out⟩
  let cfg₄ : Cfg 2 Bool RewindWorkState (u₀ ++ raw) :=
    wordsCfgAt (u₀ ++ raw) pEnd none ![List.replicate N true, u₀ ++ raw.take N] out
  have hrun₁ : ((forwardWork Bool).extendTapes (tapeEmb 1)).runFrom cfg₀ (u₀.length + 1) =
      cfg₁ := by
    have h1 : oneTapeCfg 1 cfg₀ = ⟨some (forwardWork Bool).q₀, p₀,
        fun _ => tapeOfList u₀, fun _ => ((0 : ℕ) : ℤ), out⟩ := by
      simp [oneTapeCfg, cfg₀, wordsCfgAt]
    rw [runFrom_tapeEmb, h1,
      runFrom_forwardWork p₀ u₀ out (p := 0) (n := u₀.length) (by simp), embed_tapeEmb]
    refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext i <;> fin_cases i <;>
      simp [cfg₀, cfg₁, wordsCfgAt]
  have hrun₂ : copyCappedCore.runFrom (cfg₁.withState (some copyCappedCore.q₀))
      (min N raw.length + 1) = cfg₂ := by
    simpa [cfg₁, cfg₂, Cfg.withState] using
      copyCappedCore_runFrom_halt (u₀ := u₀) (raw := raw) (out := out) (N := N)
  have hlenOut : (u₀ ++ raw.take N).length = u₀.length + min N raw.length := by
    simp [List.length_take]
  have hrun₃ : ((rewindWork Bool).extendTapes (tapeEmb 1)).runFrom
      (cfg₂.withState (some (rewindWork Bool).q₀)) (u₀.length + min N raw.length + 2) = cfg₃ := by
    have h1 : oneTapeCfg 1 (cfg₂.withState (some (rewindWork Bool).q₀)) =
        ⟨some (rewindWork Bool).q₀, pEnd, fun _ => tapeOfList (u₀ ++ raw.take N),
          fun _ => ((u₀ ++ raw.take N).length : ℤ), out⟩ :=
      Cfg.ext rfl rfl (funext fun _ => rfl)
        (funext fun _ => by simp [oneTapeCfg, cfg₂, hlenOut]) rfl
    rw [runFrom_tapeEmb,
      show u₀.length + min N raw.length + 2 = (u₀ ++ raw.take N).length + 2 by omega, h1,
      runFrom_rewindWork_none pEnd (tapeOfList (u₀ ++ raw.take N)) out rfl le_rfl, embed_tapeEmb]
    refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext i <;> fin_cases i <;>
      simp [cfg₂, cfg₃, Cfg.withState]
  have hrun₄ : ((rewindWork Bool).extendTapes (tapeEmb 0)).runFrom
      (cfg₃.withState (some (rewindWork Bool).q₀)) (min N raw.length + 2) = cfg₄ := by
    have h1 : oneTapeCfg 0 (cfg₃.withState (some (rewindWork Bool).q₀)) =
        ⟨some (rewindWork Bool).q₀, pEnd, fun _ => tapeOfList (List.replicate N true),
          fun _ => ((min N raw.length : ℕ) : ℤ), out⟩ :=
      Cfg.ext rfl rfl (funext fun _ => rfl)
        (funext fun _ => by simp [oneTapeCfg, cfg₃]) rfl
    rw [runFrom_tapeEmb, h1,
      runFrom_rewindWork_none (w := List.replicate N true) pEnd
        (tapeOfList (List.replicate N true)) out rfl (by simp),
      embed_tapeEmb]
    refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext i <;> fin_cases i <;>
      simp [cfg₃, cfg₄, wordsCfgAt, Cfg.withState]
  have hrun₁₂ := runFrom_seq hrun₁ rfl hrun₂ rfl
  have hmap₃₄ : (cfg₂.mapState (Option.map (Sum.inr : Unit → Unit ⊕ Unit))).withState
        (some rewindBothTM.q₀) =
      (cfg₂.withState (some ((rewindWork Bool).extendTapes (tapeEmb (k := 2) 1)).q₀)).mapState
        (handOver ((rewindWork Bool).extendTapes (tapeEmb (k := 2) 0)).q₀) := by
    simp [rewindBothTM, Cfg.withState, Cfg.mapState, handOver, MultiTapeTM.seq,
      MultiTapeTM.combine]
  have hrun₃₄ : rewindBothTM.runFrom
      ((cfg₂.mapState (Option.map (Sum.inr : Unit → Unit ⊕ Unit))).withState
        (some rewindBothTM.q₀))
      ((u₀.length + min N raw.length + 2) + (min N raw.length + 2)) =
      cfg₄.mapState (Option.map .inr) :=
    hmap₃₄ ▸ runFrom_seq hrun₃ rfl hrun₄ rfl
  have hstart : wordsCfgAt (u₀ ++ raw) p₀
      (some appendPrefixTM.q₀) ![List.replicate N true, u₀] out =
      (cfg₀.mapState (handOver copyCappedCore.q₀)).mapState (handOver rewindBothTM.q₀) :=
    Cfg.ext (by simp [appendPrefixTM, rewindBothTM, cfg₀, wordsCfgAt, MultiTapeTM.seq,
      MultiTapeTM.combine, MultiTapeTM.extendTapes, MultiTapeTM.adapt, handOver, Cfg.mapState])
      rfl rfl rfl rfl
  have hrunAll : appendPrefixTM.runFrom (wordsCfgAt (u₀ ++ raw) p₀
      (some appendPrefixTM.q₀) ![List.replicate N true, u₀] out)
      ((u₀.length + 1) + (min N raw.length + 1) +
        ((u₀.length + min N raw.length + 2) + (min N raw.length + 2))) =
      wordsCfgAt (u₀ ++ raw) pEnd none ![List.replicate N true, u₀ ++ raw.take N] (out ++ []) := by
    change ((((forwardWork Bool).extendTapes (tapeEmb 1)).seq copyCappedCore).seq
      rewindBothTM).runFrom _ _ = _
    rw [hstart, runFrom_seq hrun₁₂ rfl hrun₃₄ rfl]
    simp [cfg₄, wordsCfgAt, Cfg.mapState]
  refine ⟨pEnd, ![List.replicate N true, u₀ ++ raw.take N], [], hrunAll,
    ⟨rfl, rfl, rfl, rfl⟩, ?_⟩
  have hs₁₂ := (space_seq_le hrun₁ rfl (by rw [hrun₂])).trans (Nat.add_le_add
    (MultiTapeNTM.RunPath.ofDeterministic _ _ _).space_le_mul_time_add_one
    (MultiTapeNTM.RunPath.ofDeterministic _ _ _).space_le_mul_time_add_one)
  have hs₃₄ : (MultiTapeNTM.RunPath.ofDeterministic rewindBothTM
      ((cfg₂.mapState (Option.map (Sum.inr : Unit → Unit ⊕ Unit))).withState
        (some rewindBothTM.q₀))
      ((u₀.length + min N raw.length + 2) + (min N raw.length + 2))).space ≤
      ((2 * (u₀.length + min N raw.length + 2 + 1)) + (2 * (min N raw.length + 2 + 1))) := by
    rw [hmap₃₄]
    refine (space_seq_le hrun₃ rfl ?_).trans
      (Nat.add_le_add (MultiTapeNTM.RunPath.ofDeterministic _ _ _).space_le_mul_time_add_one
        (MultiTapeNTM.RunPath.ofDeterministic _ _ _).space_le_mul_time_add_one)
    erw [hrun₄]
    simp [cfg₄, wordsCfgAt, Cfg.Halted]
  change (MultiTapeNTM.RunPath.ofDeterministic
    ((((forwardWork Bool).extendTapes (tapeEmb 1)).seq copyCappedCore).seq rewindBothTM)
    _ _).space ≤ _
  rw [hstart]
  refine (space_seq_le hrun₁₂ rfl ?_).trans (Nat.add_le_add hs₁₂ hs₃₄)
  rw [hrun₃₄]
  simp [cfg₄, wordsCfgAt, Cfg.Halted, Cfg.mapState]

/-- Lift `ComputesTidilyInTimeAndSpace.onWords` onto an embedded slice of `K` tapes while leaving
all tapes outside `e` undisturbed. -/
private lemma onWords_onSlice {k K : ℕ} {Symbol State : Type*}
    {tm : MultiTapeTM k Symbol State} (mark : Symbol)
    {input output : List Symbol} {t s : ℕ}
    (h : tm.ComputesTidilyInTimeAndSpace input output t s)
    (e : Fin (k + 1 + 2) ↪ Fin K)
    {ws : Fin K → List Symbol}
    (hclean : ∀ j : Fin (k + 1 + 2), j ≠ Fin.natAdd (k + 1) 0 → ws (e j) = [])
    (hin : ws (e (Fin.natAdd (k + 1) 0)) = input) :
    TransformsTapes ((tm.onWords mark).extendTapes e)
      (fun _ v => v = ws)
      (fun _ _ v' em => v' = Function.update ws (e ((Fin.last k).castAdd 2)) output ∧ em = [])
      (t + output.length + 6)
      (s + 2 * input.length + 2 * output.length + 3 * k + 18 + (K - (k + 1 + 2))) := by
  refine ((h.onWords mark).extendTapes e).imp ?_ ?_ le_rfl le_rfl
  · rintro _ _ rfl
    funext j
    by_cases hj : j = Fin.natAdd (k + 1) 0 <;> simp [hj, hin, hclean j]
  · rintro _ _ v' em rfl ⟨⟨hv, rfl⟩, hx⟩
    refine ⟨funext fun l => ?_, rfl⟩
    by_cases hl : l ∈ Set.range e
    · obtain ⟨j, rfl⟩ := hl
      have hvj := congrFun hv j
      by_cases hj : j = (Fin.last k).castAdd 2
      · subst hj
        simpa [e.injective.eq_iff] using hvj
      · rw [Function.update_of_ne (fun h => hj (e.injective h))]
        by_cases hj2 : j = Fin.natAdd (k + 1) 0
        · subst hj2
          simpa [Function.update_apply, (Fin.castAdd_ne_natAdd _ _).symm, ← hin] using hvj
        · simpa [Function.update_apply, hj, hclean j hj2] using hvj
    · rw [hx l hl, Function.update_of_ne (fun h => hl ⟨_, h.symm⟩)]

/-- Lift `ComputesTidilyInTimeAndSpace.inputFromWord` onto an embedded slice of `K` tapes while
leaving all tapes outside `e` undisturbed. -/
private lemma inputFromWord_onSlice {k K : ℕ} {Symbol State : Type*}
    {tm : MultiTapeTM k Symbol State} (mark : Symbol)
    {input output : List Symbol} {t s : ℕ}
    (h : tm.ComputesTidilyInTimeAndSpace input output t s)
    (e : Fin (k + 2) ↪ Fin K)
    {ws : Fin K → List Symbol}
    (hclean : ∀ j : Fin (k + 2), j ≠ Fin.natAdd k 0 → ws (e j) = [])
    (hin : ws (e (Fin.natAdd k 0)) = input) :
    TransformsTapes ((tm.inputFromWord mark).extendTapes e)
      (fun _ v => v = ws)
      (fun _ _ v' em => v' = ws ∧ em = output)
      (t + 4) (s + 2 * (input.length + 2) + 2 * k + 8 + (K - (k + 2))) := by
  refine ((h.inputFromWord mark).extendTapes e).imp ?_ ?_ le_rfl le_rfl
  · rintro _ _ rfl
    refine ⟨trivial, funext fun j => ?_⟩
    by_cases hj : j = Fin.natAdd k 0 <;> simp [hj, hin, hclean j]
  · rintro _ _ v' em rfl ⟨⟨hv, rfl⟩, hx⟩
    refine ⟨funext fun l => ?_, rfl⟩
    by_cases hl : l ∈ Set.range e
    · obtain ⟨j, rfl⟩ := hl
      have hvj := congrFun hv j
      by_cases hj : j = Fin.natAdd k 0 <;> simpa [hj, hin, hclean j] using hvj
    · exact hx l hl

private lemma embed_wordsCfgAt {k k' : ℕ} {Symbol State : Type*} {input : List Symbol}
    (e : Fin k ↪ Fin k') (p : Fin (input.length + 2)) (q : Option State)
    (v : Fin k → List Symbol) {ws ws' : Fin k' → List Symbol} (out : List Symbol)
    (h : ∀ j, ws' (e j) = v j) (hx : ∀ l ∉ Set.range e, ws' l = ws l) :
    embed e (wordsCfgAt input p q v out) (fun l => tapeOfList (ws l)) (fun _ => 0) =
      wordsCfgAt input p q ws' out := by
  refine Cfg.ext rfl rfl (funext fun l => ?_) (funext fun l => ?_) rfl
  · rcases hl : partialInv e l with _ | j
    · simp [embed, hl, wordsCfgAt, hx l fun ⟨j, hj⟩ => by simp [← hj] at hl]
    · simp [embed, wordsCfgAt, ← partialInv_eq_some e hl, h]
  · simp only [embed]
    cases partialInv e l <;> rfl

/-- Lift a `TransformsTapesAt` specification onto the slice selected by `e`. -/
private theorem transformsTapesAt_extendTapes {k k' : ℕ} {Symbol State : Type*}
    {tm : MultiTapeTM k Symbol State}
    {P : (input : List Symbol) → Fin (input.length + 2) → (Fin k → List Symbol) → Prop}
    {Q : (input : List Symbol) → Fin (input.length + 2) → (Fin k → List Symbol) →
      Fin (input.length + 2) → (Fin k → List Symbol) → List Symbol → Prop} {t s : ℕ}
    (h : TransformsTapesAt tm P Q t s) (e : Fin k ↪ Fin k') :
    TransformsTapesAt (tm.extendTapes e)
      (fun input p ws => P input p fun j => ws (e j))
      (fun input p ws p' ws' emitted =>
        Q input p (fun j => ws (e j)) p' (fun j => ws' (e j)) emitted ∧
        ∀ l ∉ Set.range e, ws' l = ws l)
      t (s + (k' - k)) := by
  intro input p ws out hP
  obtain ⟨p', v, emitted, hrun, hQ, hspace⟩ := h input p (fun j => ws (e j)) out hP
  let ws' : Fin k' → List Symbol := fun l => (partialInv e l).elim (ws l) v
  have hv : ∀ j, ws' (e j) = v j := by simp [ws']
  have hx : ∀ l ∉ Set.range e, ws' l = ws l := fun l hl => by simp [ws', partialInv_eq_none e hl]
  let rp := MultiTapeNTM.RunPath.ofDeterministic tm
    (wordsCfgAt input p (some tm.q₀) (fun j => ws (e j)) out) t
  let rq := rp.map (embedHom tm e (fun l => tapeOfList (ws l)) (fun _ => 0))
  have hrqHead : rq.head = wordsCfgAt input p (some (tm.extendTapes e).q₀) ws out := by
    simp only [rq, RelSeries.head_map, rp, embedHom_apply, extendTapes_q₀]
    exact embed_wordsCfgAt e p (some tm.q₀) (fun j => ws (e j)) out (fun _ => rfl) fun _ _ => rfl
  have hrqLast : rq.last = wordsCfgAt input p' none ws' (out ++ emitted) := by
    have hrpLast : rp.last = wordsCfgAt input p' none v (out ++ emitted) :=
      (runPath_last_eq_runFrom rp).trans hrun
    simp only [rq, RelSeries.last_map, hrpLast, embedHom_apply]
    exact embed_wordsCfgAt e p' none v (out ++ emitted) hv hx
  have hrunQ : (tm.extendTapes e).runFrom (wordsCfgAt input p (some (tm.extendTapes e).q₀) ws out)
      t = wordsCfgAt input p' none ws' (out ++ emitted) := by
    rw [← hrqHead, show t = rq.length from rfl, ← runPath_last_eq_runFrom rq, hrqLast]
  have hspQ : rq.space ≤ s + (k' - k) :=
    (space_map_embedHom_le ..).trans (Nat.add_le_add_right hspace _)
  refine ⟨p', ws', emitted, hrunQ, ⟨by simpa only [hv] using hQ, hx⟩,
    (MultiTapeNTM.RunPath.space_le_of_subset ?_).trans hspQ⟩
  rintro _ ⟨n, rfl⟩
  rw [runPath_apply_eq_runFrom,
    show (MultiTapeNTM.RunPath.ofDeterministic _ _ _).head = rq.head by rw [hrqHead]; rfl]
  exact ⟨⟨n.val, n.isLt⟩, runPath_apply_eq_runFrom rq ⟨n.val, n.isLt⟩⟩

private def embUIdx (kU j : ℕ) : ℕ :=
  if j < kU then 3 + j
  else if j = kU then 1
  else if j = kU + 1 then 0
  else 3 + kU

private lemma embUIdx_lt (kU kC kV j : ℕ) :
    embUIdx kU j < 3 + (kU + 1) + (kC + 1) + (kV + 1) := by
  unfold embUIdx
  split_ifs <;> omega

private lemma embUIdx_inj (kU : ℕ) {a b : ℕ} (ha : a < kU + 1 + 2) (hb : b < kU + 1 + 2)
    (h : embUIdx kU a = embUIdx kU b) : a = b := by
  unfold embUIdx at h
  split_ifs at h <;> omega

private def embCIdx (kU kC j : ℕ) : ℕ :=
  if j < kC then 3 + (kU + 1) + j
  else if j = kC then 2
  else if j = kC + 1 then 1
  else 3 + (kU + 1) + kC

private lemma embCIdx_lt (kU kC kV j : ℕ) :
    embCIdx kU kC j < 3 + (kU + 1) + (kC + 1) + (kV + 1) := by
  unfold embCIdx
  split_ifs <;> omega

private lemma embCIdx_inj (kU kC : ℕ) {a b : ℕ} (ha : a < kC + 1 + 2) (hb : b < kC + 1 + 2)
    (h : embCIdx kU kC a = embCIdx kU kC b) : a = b := by
  unfold embCIdx at h
  split_ifs at h <;> omega

private def embVIdx (kU kC kV j : ℕ) : ℕ :=
  if j < kV then 3 + (kU + 1) + (kC + 1) + j
  else if j = kV then 0
  else 3 + (kU + 1) + (kC + 1) + kV

private lemma embVIdx_lt (kU kC kV j : ℕ) :
    embVIdx kU kC kV j < 3 + (kU + 1) + (kC + 1) + (kV + 1) := by
  unfold embVIdx
  split_ifs <;> omega

private lemma embVIdx_inj (kU kC kV : ℕ) {a b : ℕ} (ha : a < kV + 2) (hb : b < kV + 2)
    (h : embVIdx kU kC kV a = embVIdx kU kC kV b) : a = b := by
  unfold embVIdx at h
  split_ifs at h <;> omega

private def embU (kU kC kV : ℕ) :
    Fin (kU + 1 + 2) ↪ Fin (3 + (kU + 1) + (kC + 1) + (kV + 1)) where
  toFun j := ⟨embUIdx kU j.val, embUIdx_lt kU kC kV j.val⟩
  inj' a b h := Fin.ext (embUIdx_inj kU a.isLt b.isLt (congrArg Fin.val h))

private def embC (kU kC kV : ℕ) :
    Fin (kC + 1 + 2) ↪ Fin (3 + (kU + 1) + (kC + 1) + (kV + 1)) where
  toFun j := ⟨embCIdx kU kC j.val, embCIdx_lt kU kC kV j.val⟩
  inj' a b h := Fin.ext (embCIdx_inj kU kC a.isLt b.isLt (congrArg Fin.val h))

private def embCopy (kU kC kV : ℕ) :
    Fin 2 ↪ Fin (3 + (kU + 1) + (kC + 1) + (kV + 1)) where
  toFun j := if j.val = 0 then ⟨2, by omega⟩ else ⟨0, by omega⟩
  inj' a b h := by
    have hval := congrArg Fin.val h
    fin_cases a <;> fin_cases b <;> simp_all

private def embV (kU kC kV : ℕ) :
    Fin (kV + 2) ↪ Fin (3 + (kU + 1) + (kC + 1) + (kV + 1)) where
  toFun j := ⟨embVIdx kU kC kV j.val, embVIdx_lt kU kC kV j.val⟩
  inj' a b h := Fin.ext (embVIdx_inj kU kC kV a.isLt b.isLt (congrArg Fin.val h))

private lemma embU_input (kU kC kV : ℕ) :
    embU kU kC kV (Fin.natAdd (kU + 1) 0) = ⟨0, by omega⟩ :=
  Fin.ext (by simp [embU, embUIdx])

private lemma embU_output (kU kC kV : ℕ) :
    embU kU kC kV ((Fin.last kU).castAdd 2) = ⟨1, by omega⟩ :=
  Fin.ext (by simp [embU, embUIdx])

private lemma embC_input (kU kC kV : ℕ) :
    embC kU kC kV (Fin.natAdd (kC + 1) 0) = ⟨1, by omega⟩ :=
  Fin.ext (by simp [embC, embCIdx])

private lemma embC_output (kU kC kV : ℕ) :
    embC kU kC kV ((Fin.last kC).castAdd 2) = ⟨2, by omega⟩ :=
  Fin.ext (by simp [embC, embCIdx])

private lemma embV_input (kU kC kV : ℕ) :
    embV kU kC kV (Fin.natAdd kV 0) = ⟨0, by omega⟩ :=
  Fin.ext (by simp [embV, embVIdx])

private lemma embU_val_ne_zero (kU kC kV : ℕ) (j : Fin (kU + 1 + 2))
    (hj : j ≠ Fin.natAdd (kU + 1) 0) :
    (embU kU kC kV j).val ≠ 0 := by
  change embUIdx kU j.val ≠ 0
  unfold embUIdx
  split_ifs with h0 h1 h2 <;> first | omega | exact absurd (Fin.ext (by simp [h2])) hj

private lemma embC_val_ge_two (kU kC kV : ℕ) (j : Fin (kC + 1 + 2))
    (hj : j ≠ Fin.natAdd (kC + 1) 0) :
    2 ≤ (embC kU kC kV j).val := by
  change 2 ≤ embCIdx kU kC j.val
  unfold embCIdx
  split_ifs with h0 h1 h2 <;> first | omega | exact absurd (Fin.ext (by simp [h2])) hj

private lemma embV_val_ge_three (kU kC kV : ℕ) (j : Fin (kV + 2))
    (hj : j ≠ Fin.natAdd kV 0) :
    3 ≤ (embV kU kC kV j).val := by
  change 3 ≤ embVIdx kU kC kV j.val
  unfold embVIdx
  split_ifs with h0 h1 <;> first | omega | exact absurd (Fin.ext (by simp [h1])) hj

end Helpers

public section

/-- Any polynomial-time function `f : α × List Bool → β` whose value on `(a, raw)` depends only on
`raw.take (cap a + 1)` — where `cap : α → ℕ` is unary polynomial-time — can be computed by one
multi-tape Turing machine whose worst-case time and space on `(a, raw)` are bounded by polynomials
in `(encA a).length` alone, independent of `raw.length`. -/
theorem computableInTimeAndSpace_boundedPrefix
    {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {cap : α → ℕ} {f : α × List Bool → β}
    (hcap : ComputableInPolyTime cap encA encUnary)
    (hf : ComputableInPolyTime f (encPair encA encBits) encB)
    (hagree : ∀ a (raw : List Bool), f (a, raw) = f (a, raw.take (cap a + 1))) :
    ∃ (k : ℕ) (State : Type) (_ : Finite State) (tm : MultiTapeTM k Bool State)
      (t s : ℕ → ℕ),
      PolynomiallyBounded t ∧ PolynomiallyBounded s ∧
      tm.ComputesFunInTimeAndSpace (encPair encA encBits) encB f
        (fun p => t (encA p.1).length)
        (fun p => s (encA p.1).length) := by
  have hunframe : ComputableInPolyTime unframe encBits encBits :=
    Internal.DecoderWords.unframe_degree.computableInPolyTime
  have hcapSucc : ComputableInPolyTime (fun a => cap a + 1) encA encUnary :=
    ComputableInPolyTime.unary_add' hcap (ComputableInPolyTime.const 1)
  obtain ⟨cU, dU, kU, SU, hfinU, tmU, htmU⟩ := Internal.NormalForm.polyTime hunframe
  obtain ⟨cC, dC, kC, SC, hfinC, tmC, htmC⟩ := Internal.NormalForm.polyTime hcapSucc
  obtain ⟨cV, dV, kV, SV, hfinV, tmV, htmV⟩ := Internal.NormalForm.polyTime hf
  let K : ℕ := 3 + (kU + 1) + (kC + 1) + (kV + 1)
  let tV : Fin K := ⟨0, by omega⟩
  let tU : Fin K := ⟨1, by omega⟩
  let tCap : Fin K := ⟨2, by omega⟩
  let m1 := appendRead frameStopReader tV
  let m2 := ((tmU.onWords true).extendTapes (embU kU kC kV)).freezeInput
  let m3 := ((tmC.onWords true).extendTapes (embC kU kC kV)).freezeInput
  let m4 := appendPrefixTM.extendTapes (embCopy kU kC kV)
  let m5 := ((tmV.inputFromWord true).extendTapes (embV kU kC kV)).freezeInput
  let M := m1.seq (m2.seq (m3.seq (m4.seq m5)))
  let capBound (L : ℕ) : ℕ := cC * (L + 1) ^ dC
  let wBound (L : ℕ) : ℕ := 2 * L + 1 + capBound L
  let tPoly (L : ℕ) : ℕ :=
    (2 * (2 * L + 1) + 4) +
    ((cU * ((2 * L + 1) + 1) ^ dU + L + 6) +
    ((2 * capBound L + 6) +
    ((2 * L + 1 + 1 + (capBound L + 1) + (2 * L + 1 + capBound L + 2) + (capBound L + 2)) +
    (cV * (wBound L + 1) ^ dV + 4))))
  let sPoly (L : ℕ) : ℕ :=
    ((2 * L + 1) + 2 + (K - 1)) +
    ((cU * ((2 * L + 1) + 1) ^ dU + 2 * (2 * L + 1) + 2 * L + 3 * kU + 18 +
      (K - (kU + 1 + 2))) +
    ((capBound L + 2 * L + 2 * capBound L + 3 * kC + 18 + (K - (kC + 1 + 2))) +
    (((2 * (2 * L + 1 + 1 + 1)) + 2 * (capBound L + 1 + 1) +
      ((2 * (2 * L + 1 + capBound L + 2 + 1)) + (2 * (capBound L + 2 + 1))) + (K - 2)) +
    (cV * (wBound L + 1) ^ dV + 2 * (wBound L + 2) + 2 * kV + 8 + (K - (kV + 2))))))
  refine ⟨K, _, inferInstance, M, tPoly, sPoly, ?_, ?_, fun p => ?_⟩
  · dsimp only [tPoly, wBound, capBound]
    fun_prop
  · dsimp only [sPoly, wBound, capBound]
    fun_prop
  · rcases p with ⟨a, raw⟩
    let u := encA a
    let N := cap a + 1
    let L := u.length
    let inp := encPair encA encBits (a, raw)
    have hinp : inp = frame u ++ raw := by simp [inp, encPair_apply, encBits_apply, u]
    have hNle : N ≤ capBound L := by
      simpa [encUnary_apply, N, L, u, capBound] using (htmC a).length_output_le
    have hlenFrame : (frame u).length = 2 * L + 1 := by simp [length_frame, u, L]
    let ws₀ : Fin K → List Bool := fun _ => []
    let ws₁ : Fin K → List Bool := Function.update ws₀ tV (frame u)
    let ws₂ : Fin K → List Bool := Function.update ws₁ tU u
    let ws₃ : Fin K → List Bool := Function.update ws₂ tCap (encUnary N)
    let ws₄ : Fin K → List Bool := Function.update ws₃ tV (frame u ++ raw.take N)
    let p₁ : ℕ := 1 + (frame u).length
    let p₂ : ℕ := p₁ + min N raw.length
    have hspec1 : TransformsWordsAt m1 inp 1 p₁ ws₀ ws₁ []
        (2 * (frame u).length + 4) ((frame u).length + 2 + (K - 1)) := by
      have hr := transformsTapesAt_appendRead frameStopReader tV inp ⟨1, by simp⟩ (by simp) []
      have hread : frameStopReader.read frameStopReader.q₀ (inp.drop (1 - 1)) =
          (frame u, (frame u).length) := by
        simpa [frameStopReader, hinp] using read_frameStopReader u raw
      have hwords := hr.wordsAt (p := 1) (p' := 1 + (frameStopReader.read frameStopReader.q₀
          (inp.drop (1 - 1))).2) (ws := ws₀)
        (ws' := Function.update ws₀ tV ([] ++ (frameStopReader.read frameStopReader.q₀
          (inp.drop (1 - 1))).1))
        (e := []) (fun q hq => ⟨rfl, hq, by simp [ws₀]⟩) (fun _ _ _ _ _ hQ => hQ)
      have hwords' := hwords.congr rfl (by rw [hread]) rfl (by rw [hread]) rfl
      refine hwords'.mono ?_ ?_
      · simp only [hread, List.nil_append, List.length_nil, Nat.zero_add]; omega
      · simp only [hread, List.nil_append, le_rfl]
    have hspec2 : TransformsWordsAt m2 inp p₁ p₁ ws₁ ws₂ []
        (cU * ((frame u).length + 1) ^ dU + L + 6)
        (cU * ((frame u).length + 1) ^ dU + 2 * (frame u).length + 2 * L + 3 * kU + 18 +
          (K - (kU + 1 + 2))) := by
      have hslice := onWords_onSlice true (tm := tmU) (input := frame u) (output := u)
        (by simpa [unframe_frame] using htmU (frame u)) (embU kU kC kV) (ws := ws₁)
        (fun j hj => by
          have hneV : embU kU kC kV j ≠ tV :=
            Fin.ne_of_val_ne (embU_val_ne_zero kU kC kV j hj)
          simp [ws₁, ws₀, Function.update_of_ne hneV])
        (by simp [embU_input, ws₁, tV])
      have hW := hslice.words (fun _ => rfl) (fun _ _ _ ⟨hv, he⟩ =>
        ⟨by simpa [ws₂, tU, embU_output] using hv, he⟩)
      exact (by simpa [hlenFrame, L] using hW : TransformsWords _ ws₁ ws₂ [] _ _).freezeInput inp p₁
    have hspec3 : TransformsWordsAt m3 inp p₁ p₁ ws₂ ws₃ []
        (cC * (L + 1) ^ dC + (encUnary N).length + 6)
        (cC * (L + 1) ^ dC + 2 * L + 2 * (encUnary N).length + 3 * kC + 18 +
          (K - (kC + 1 + 2))) := by
      have hslice := onWords_onSlice true (tm := tmC) (input := u) (output := encUnary N)
        (htmC a) (embC kU kC kV) (ws := ws₂)
        (fun j hj => by
          have hge := embC_val_ge_two kU kC kV j hj
          have hneU : embC kU kC kV j ≠ tU := Fin.ne_of_val_ne (by dsimp [tU]; omega)
          have hneV : embC kU kC kV j ≠ tV := Fin.ne_of_val_ne (by dsimp [tV]; omega)
          simp [ws₂, ws₁, ws₀, Function.update_of_ne hneU, Function.update_of_ne hneV])
        (by simp [embC_input, ws₂, tU])
      have hW := hslice.words (fun _ => rfl) (fun _ _ _ ⟨hv, he⟩ =>
        ⟨by simpa [ws₃, tCap, embC_output] using hv, he⟩)
      exact (by simpa [L, u, N, ws₃, tCap, K] using hW :
        TransformsWords _ ws₂ ws₃ [] _ _).freezeInput inp p₁
    have hspec4 : TransformsWordsAt m4 inp p₁ p₂ ws₃ ws₄ []
        (((frame u).length + 1) + (min N raw.length + 1) +
          (((frame u).length + min N raw.length + 2) + (min N raw.length + 2)))
        ((2 * ((frame u).length + 1 + 1)) + (2 * (min N raw.length + 1 + 1)) +
          ((2 * ((frame u).length + min N raw.length + 2 + 1)) +
            (2 * (min N raw.length + 2 + 1))) + (K - 2)) := by
      refine (transformsTapesAt_extendTapes
        (transformsWordsAt_appendPrefixTM (frame u) raw N) (embCopy kU kC kV)).wordsAt
        (fun _ hq => ⟨hinp, hq, funext fun j => by
          fin_cases j
          · simp [embCopy, ws₃, tCap]
          · simp [embCopy, ws₃, ws₂, ws₁, tCap, tU, tV]⟩)
        (fun _ _ _ _ _ ⟨⟨_, hq', hv, he⟩, hx⟩ =>
          ⟨by simpa [p₂, p₁] using hq', funext fun l => ?_, he⟩)
      by_cases hl : l ∈ Set.range (embCopy kU kC kV)
      · obtain ⟨j, rfl⟩ := hl
        have hj := congrFun hv j
        fin_cases j
        · simpa [embCopy, ws₄, ws₃, tCap, tV, Function.update_apply, encUnary_apply] using hj
        · simpa [embCopy, ws₄, tV, Function.update_apply] using hj
      · rw [hx l hl]
        have hneV : l ≠ tV := fun h => hl ⟨1, by simp [embCopy, h, tV]⟩
        simp [ws₄, Function.update_of_ne hneV]
    have hspec5 : TransformsWordsAt m5 inp p₂ p₂ ws₄ ws₄
        (encB (f (a, raw.take N)))
        (cV * ((frame u ++ raw.take N).length + 1) ^ dV + 4)
        (cV * ((frame u ++ raw.take N).length + 1) ^ dV +
          2 * ((frame u ++ raw.take N).length + 2) + 2 * kV + 8 + (K - (kV + 2))) := by
      have hslice := inputFromWord_onSlice true (tm := tmV)
        (input := encPair encA encBits (a, raw.take N)) (output := encB (f (a, raw.take N)))
        (htmV (a, raw.take N)) (embV kU kC kV) (ws := ws₄)
        (fun j hj => by
          have hge := embV_val_ge_three kU kC kV j hj
          have hneV : embV kU kC kV j ≠ tV := Fin.ne_of_val_ne (by dsimp [tV]; omega)
          have hneCap : embV kU kC kV j ≠ tCap := Fin.ne_of_val_ne (by dsimp [tCap]; omega)
          have hneU : embV kU kC kV j ≠ tU := Fin.ne_of_val_ne (by dsimp [tU]; omega)
          simp [ws₄, ws₃, ws₂, ws₁, ws₀, Function.update_of_ne hneV, Function.update_of_ne hneCap,
            Function.update_of_ne hneU])
        (by simp [embV_input, ws₄, tV, encPair_apply, encBits_apply, u])
      simpa [encPair_apply, encBits_apply, u] using
        (hslice.words (fun _ => rfl) fun _ _ _ h => h).freezeInput inp p₂
    have hcomp := (hspec1.seq (hspec2.seq (hspec3.seq (hspec4.seq hspec5)))).congr
      (e₂ := encB (f (a, raw))) rfl rfl rfl rfl (by simp [N, ← hagree a raw])
    have hlen1 : (encUnary N).length ≤ capBound L := by simpa [encUnary_apply] using hNle
    have hmin : min N raw.length ≤ capBound L := (min_le_left _ _).trans hNle
    have hW : (frame u ++ raw.take N).length ≤ wBound L := by
      simp only [List.length_append, hlenFrame, List.length_take, wBound]; omega
    have hpow : cV * ((frame u ++ raw.take N).length + 1) ^ dV ≤ cV * (wBound L + 1) ^ dV := by
      gcongr
    have ht_le : (2 * (frame u).length + 4) +
        ((cU * ((frame u).length + 1) ^ dU + L + 6) +
        ((cC * (L + 1) ^ dC + (encUnary N).length + 6) +
        ((((frame u).length + 1) + (min N raw.length + 1) +
          (((frame u).length + min N raw.length + 2) + (min N raw.length + 2))) +
        (cV * ((frame u ++ raw.take N).length + 1) ^ dV + 4)))) ≤ tPoly L := by
      dsimp only [tPoly, wBound, capBound] at hlen1 hmin hW hpow ⊢
      rw [hlenFrame]
      omega
    have hs_le : ((frame u).length + 2 + (K - 1)) +
        ((cU * ((frame u).length + 1) ^ dU + 2 * (frame u).length + 2 * L + 3 * kU + 18 +
          (K - (kU + 1 + 2))) +
        ((cC * (L + 1) ^ dC + 2 * L + 2 * (encUnary N).length + 3 * kC + 18 +
          (K - (kC + 1 + 2))) +
        (((2 * ((frame u).length + 1 + 1)) + (2 * (min N raw.length + 1 + 1)) +
          ((2 * ((frame u).length + min N raw.length + 2 + 1)) +
            (2 * (min N raw.length + 2 + 1))) + (K - 2)) +
        (cV * ((frame u ++ raw.take N).length + 1) ^ dV +
          2 * ((frame u ++ raw.take N).length + 2) + 2 * kV + 8 + (K - (kV + 2)))))) ≤ sPoly L := by
      dsimp only [sPoly, wBound, capBound] at hlen1 hmin hW hpow ⊢
      rw [hlenFrame]
      omega
    obtain ⟨p', ws', _, hrun, ⟨_, _, _, rfl⟩, hspace⟩ :=
      (hcomp.mono ht_le hs_le) inp 1 ws₀ [] ⟨rfl, rfl, rfl⟩
    obtain ⟨rp, hrpHead, hrpLast, hrpLen, hrpSpace⟩ := (exists_runPath_iff_runFrom rfl).mpr
      ⟨by simpa [M, wordsCfgAt, Cfg.init_eq_wordsCfg, ws₀] using hrun,
       by simpa [M, wordsCfgAt, Cfg.init_eq_wordsCfg, ws₀] using hspace⟩
    exact computesInTimeAndSpace_iff_exists_runPath.mpr
      ⟨rp, hrpHead, by rw [hrpLast], by rw [hrpLast], hrpLen, hrpSpace⟩

end

end Turing.MultiTapeTM
