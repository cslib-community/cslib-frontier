/-
Copyright (c) 2026 Clément Trecourt, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clément Trecourt, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Halting.Basic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.ClearWork
import CslibFrontier.Computability.Machines.Turing.MultiTape.Combinators.CopyWord
import CslibFrontier.Computability.Machines.Turing.MultiTape.Combinators.IterateWhileLayout
-- `import all` avoids modifying the `Internal.KernelComp` hub while unfolding unexposed
-- `Turing.MultiTapeTM.comp`.
import all CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.KernelComp
-- `import all` reads the private `IterateWhile.transformsTapes_{load,emit,clearCur,onWords_step}`
-- lemmas from `Internal.KernelIterateWhile` without modifying that vendored hub.
import all CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.KernelIterateWhile
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.KernelOnWords
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NormalForm
import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.InputFromTape
import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.OutputToTape
import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.Sequential
import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.WhileCond
import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.WhileCond.Partial
import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.WordsCfg
import Mathlib.Tactic.Linarith

/-!
# Partial iteration of polynomial-time steps

`Turing.MultiTapeTM.exists_partial_iterateWhile` packages a polynomial-time `init`, `step`, and
`fin` into one fixed binary multi-tape Turing machine with finitely many states that iterates
`step` from `init a` until the encoded state becomes empty (`[]`), then applies `fin` to the last
non-empty state.

Unlike `Turing.MultiTapeTM.exists_computableInTimeAndSpace_iterateWhile`, termination is not assumed
globally:
* on any input `a` whose trajectory first hits the empty encoding after `r + 1` rounds, with all
  states up to round `r` encoded within `l` bits, the machine halts with `fin (step^[r] (init a))`
  within time `c * (r + 1) * (l + |encIn a| + 1) ^ d` and space `c * (l + |encIn a| + 1) ^ d`;
* on any input `a` whose trajectory never hits the empty encoding, the machine diverges
  (`¬ tm.Halts (encIn a)`).

This is the native machine-level loop underlying unbounded dovetailed searches such as Levin's
universal search.

## Main results

* `Turing.MultiTapeTM.exists_partial_iterateWhile`: one fixed machine with certified time and space
  on terminating trajectories and proved divergence on non-terminating trajectories.
-/

public section

namespace Turing.MultiTapeTM

section Machinery

open IterateWhile

variable {k : ℕ} {Symbol State State₀ State₁ : Type*} {input : List Symbol}

/-! ### Local loop machine -/

/-- Condition testing whether the next-word tape `nextTape k` is non-empty. -/
private def nextNonEmpty (k : ℕ) (Symbol : Type*) :
    Option Symbol → (Fin (k + 1 + 2) → Option Symbol) → Bool :=
  fun _ work => (work (nextTape k)).isSome

/-- One round of the partial iterate-while loop: move the next word to the current tape and run
`tm` from the current tape to the next tape. -/
private noncomputable def loopRound (tm : MultiTapeTM k Symbol State) (mark : Symbol) :=
  (IterateWhile.prepareRound (k := k) mark).seq (tm.onWords mark)

/-- Load the input onto the next tape, run `loopRound` once and then while `nextTape k` is
non-empty, then emit the current word and clear its tape. -/
private noncomputable def loopMachine (tm : MultiTapeTM k Symbol State) (mark : Symbol) :=
  (loadWord Symbol (nextTape k)).seq
    ((loopRound tm mark).seq
      ((whileCond (nextNonEmpty k Symbol) (loopRound tm mark)).seq
        ((emitWord (emitEmb k) mark).seq ((clearWork Symbol).extendTapes (tapeEmb (curTape k))))))

/-! ### Terminating specifications -/

private lemma transformsTapes_loopRound {tm : MultiTapeTM k Symbol State} (mark : Symbol)
    {vp v v' : List Symbol} {t s : ℕ} (h : tm.ComputesTidilyInTimeAndSpace v v' t s) :
    TransformsTapes (loopRound tm mark) (fun _ ws => ws = words vp v)
      (fun _ _ ws' e => ws' = words v v' ∧ e = [])
      (t + 3 * vp.length + 6 * v.length + v'.length + 22)
      (s + vp.length + 7 * v.length + 2 * v'.length + 6 * k + 44) :=
  ((transformsTapes_prepareRound (k := k) mark vp v).seq_eq
    (transformsTapes_onWords_step mark h)).imp
    (fun _ _ h => h) (fun _ _ _ _ _ ⟨h', he⟩ => ⟨h', by simp [he]⟩) (by omega) (by omega)

private lemma condAt_nextNonEmpty (p : Fin (input.length + 2)) (vc vn : List Symbol) :
    condAt (nextNonEmpty k Symbol) input p (words (k := k) vc vn) = vn.head?.isSome := by
  simp [condAt, nextNonEmpty]

private theorem computesTidily_loopMachine {tm : MultiTapeTM k Symbol State}
    {w : ℕ → List Symbol} {r t s l : ℕ}
    (h : ∀ n ≤ r, tm.ComputesTidilyInTimeAndSpace (w n) (w (n + 1)) t s)
    (hl : ∀ n ≤ r, (w n).length ≤ l) (hne : ∀ n < r, w (n + 1) ≠ []) (hnil : w (r + 1) = [])
    (mark : Symbol) :
    (loopMachine tm mark).ComputesTidilyInTimeAndSpace (w 0) (w r)
      ((r + 1) * (t + 10 * l + 24) + 8 * l + 18)
      ((2 * (k + 3) + 1) * (s + 10 * l + 6 * k + 44) + 5 * l + 4 * k + 26) := by
  have hl' (n : ℕ) (hn : n ≤ r) : (w (n + 1)).length ≤ l := by
    rcases hn.lt_or_eq with hn | rfl
    exacts [hl _ hn, by simp [hnil]]
  have hfirstRound : TransformsTapes (loopRound tm mark) (fun _ ws => ws = words [] (w 0))
      (fun _ _ ws' e => ws' = words (w 0) (w 1) ∧ e = [])
      (t + 10 * l + 23) (s + 10 * l + 6 * k + 44) := by
    have := hl 0 (Nat.zero_le r)
    have := hl' 0 (Nat.zero_le r)
    exact (transformsTapes_loopRound mark (vp := []) (h 0 (Nat.zero_le r))).mono
      (by simp only [List.length_nil]; omega) (by simp only [List.length_nil]; omega)
  have hlaterRound (n : ℕ) (hn : n < r) :
      TransformsTapes (loopRound tm mark) (fun _ ws => ws = words (w n) (w (n + 1)))
        (fun _ _ ws' e => ws' = words (w (n + 1)) (w (n + 2)) ∧ e = [])
        (t + 10 * l + 23) (s + 10 * l + 6 * k + 44) := by
    have := hl n hn.le; have := hl (n + 1) hn; have := hl' (n + 1) hn
    exact (transformsTapes_loopRound mark (vp := w n) (h (n + 1) hn)).mono (by omega) (by omega)
  have hwhileAt := transformsTapesAt_whileCond (c := nextNonEmpty k Symbol)
    (tm := loopRound tm mark)
    (P := fun n _ p ws emitted => p = 1 ∧ ws = words (w n) (w (n + 1)) ∧ emitted = [])
    (R := fun _ p ws emitted => p = 1 ∧ ws = words (w r) [] ∧ emitted = [])
    (rounds := r) (t := fun _ => t + 10 * l + 23) (s := s + 10 * l + 6 * k + 44)
    (fun n hn _ => (hlaterRound n hn).transformsTapesAt.imp
      (fun _ _ _ ⟨hp, hws, _⟩ => ⟨hp, hws⟩)
      (fun _ _ _ _ _ _ ⟨_, _, hem⟩ ⟨hp', hws', he⟩ => ⟨hp', hws', by simp [hem, he]⟩)
      le_rfl le_rfl)
    (fun n hn _ p ws _ ⟨_, hws, _⟩ => by
      rw [hws, condAt_nextNonEmpty]
      cases hwn : w (n + 1) with
      | nil => exact absurd hwn (hne n hn)
      | cons _ _ => rfl)
    (fun _ p ws _ ⟨hp, hws, hem⟩ => by
      rw [hws, hnil]
      exact ⟨by simp [condAt_nextNonEmpty], hp, rfl, hem⟩)
  have hwhile : TransformsTapes (whileCond (nextNonEmpty k Symbol) (loopRound tm mark))
      (fun _ ws => ws = words (w 0) (w 1))
      (fun _ _ ws' e => ws' = words (w r) [] ∧ e = [])
      (r * (t + 10 * l + 24) + 1)
      (2 * (k + 3) * (s + 10 * l + 6 * k + 44) + (k + 3)) := by
    rw [transformsTapes_iff_runFrom]
    intro inp ws out hws
    obtain ⟨p', ws', e, hrun, ⟨hp', hws', he⟩, hsp⟩ := hwhileAt inp 1 ws out ⟨rfl, hws, rfl⟩
    subst hp'
    have hsum : (∑ _ ∈ Finset.range r, (t + 10 * l + 23 + 1)) + 1 = r * (t + 10 * l + 24) + 1 := by
      simp [Finset.sum_const]
    exact ⟨ws', e, hsum ▸ hrun, ⟨hws', he⟩, hsum ▸ hsp⟩
  refine ((transformsTapes_load (k := k) (w 0)).seq_eq
    ((hfirstRound.seq_eq (hwhile.seq_eq
      ((transformsTapes_emit mark (w r)).seq_eq (transformsTapes_clearCur Symbol (w r) [])))))).imp
    (fun _ _ h => h) (fun _ _ _ _ _ ⟨hws, he⟩ => ⟨hws.trans words_nil_nil, by simp [he]⟩) ?_ ?_
  all_goals
    have := hl 0 (Nat.zero_le _)
    have := hl r le_rfl
    ring_nf
    omega

/-! ### Divergence preservation -/

private lemma initCfg_seq_eq_wordsCfg {tm₀ : MultiTapeTM k Symbol State₀}
    {tm₁ : MultiTapeTM k Symbol State₁} (x : List Symbol) :
    (tm₀.seq tm₁).initCfg x =
      (wordsCfg x (some tm₀.q₀) (fun _ => []) []).mapState (handOver tm₁.q₀) := by
  refine Cfg.ext rfl rfl (funext fun _ => ?_) rfl rfl
  simp [Cfg.mapState, wordsCfg, tapeOfList_nil, Cfg.init, MultiTapeNTM.initCfg]

private lemma not_halted_mapState {State' : Type*} {cfg : Cfg k Symbol State input}
    {f : Option State → Option State'} (hf : ∀ q, f (some q) ≠ none) (h : ¬cfg.Halted) :
    ¬(cfg.mapState f).Halted := by
  cases hq : cfg.state with
  | none => simp [Cfg.Halted, hq] at h
  | some q => simp [Cfg.Halted, Cfg.mapState, hq, hf]

private theorem not_halted_seq_of_left {tm₀ : MultiTapeTM k Symbol State₀}
    {tm₁ : MultiTapeTM k Symbol State₁} {cfg : Cfg k Symbol State₀ input}
    (h₀ : ∀ t, ¬(tm₀.runFrom cfg t).Halted) (t : ℕ) :
    ¬((tm₀.seq tm₁).runFrom (cfg.mapState (handOver tm₁.q₀)) t).Halted := by
  rw [seq, runFrom_combine_left (handOver_some _) cfg fun s _ => h₀ s]
  exact not_halted_mapState (fun _ => by simp [handOver]) (h₀ t)

private theorem not_halted_seq_of_right {tm₀ : MultiTapeTM k Symbol State₀}
    {tm₁ : MultiTapeTM k Symbol State₁} {cfg mid : Cfg k Symbol State₀ input} {t₀ : ℕ}
    (h₀ : tm₀.runFrom cfg t₀ = mid) (hmid : mid.Halted)
    (h₁ : ∀ t, ¬(tm₁.runFrom (mid.withState (some tm₁.q₀)) t).Halted) (t : ℕ) :
    ¬((tm₀.seq tm₁).runFrom (cfg.mapState (handOver tm₁.q₀)) t).Halted := by
  obtain ⟨u, hu, hhaltsAt⟩ := exists_haltsAt (tm := tm₀) (cfg := cfg) (h₀ ▸ hmid)
  rcases Nat.lt_or_ge t u with ht | ht
  · rw [seq, hhaltsAt.runFrom_combine_left (handOver_some _) ht.le]
    exact not_halted_mapState (fun _ => by simp [handOver]) (hhaltsAt.not_halted ht)
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le ht
    rw [hhaltsAt.runFrom_seq, ← hhaltsAt.runFrom_eq hu, h₀]
    exact not_halted_mapState (fun _ => by simp) (h₁ n)

private theorem not_halts_loopMachine {tm : MultiTapeTM k Symbol State}
    {w : ℕ → List Symbol}
    (hstep : ∀ n, ∃ t s, tm.ComputesTidilyInTimeAndSpace (w n) (w (n + 1)) t s)
    (hne : ∀ n, w (n + 1) ≠ []) (mark : Symbol) :
    ¬(loopMachine tm mark).Halts (w 0) := by
  rintro ⟨t, hhalt⟩
  obtain ⟨ws₀, e₀, hloadRun, ⟨hws₀, he₀⟩, -⟩ := transformsTapes_iff_runFrom.mp
    (transformsTapes_load (k := k) (w 0)) (w 0) (fun _ => []) [] ⟨rfl, rfl⟩
  rw [hws₀, he₀, List.nil_append] at hloadRun
  obtain ⟨t₀, s₀, h0⟩ := hstep 0
  obtain ⟨ws₁, e₁, hfirstRun, ⟨hws₁, he₁⟩, -⟩ := transformsTapes_iff_runFrom.mp
    (transformsTapes_loopRound mark (vp := []) h0) (w 0) (words [] (w 0)) [] rfl
  rw [hws₁, he₁, List.nil_append] at hfirstRun
  let cfg : ℕ → Cfg (k + 1 + 2) Symbol Unit (w 0) :=
    fun n => wordsCfg (w 0) none (words (w n) (w (n + 1))) []
  have hcond : ∀ n, nextNonEmpty k Symbol (cfg n).inputSymbol (cfg n).workTapeSymbols = true := by
    intro n
    have hsym : (cfg n).workTapeSymbols (nextTape k) = (w (n + 1)).head? := by
      simp [cfg, Cfg.workTapeSymbols, wordsCfg, tapeOfList_zero, words_next]
    simp only [nextNonEmpty, hsym]
    cases hwn : w (n + 1) with
    | nil => exact absurd hwn (hne n)
    | cons _ _ => rfl
  have hbody : ∀ n, nextNonEmpty k Symbol (cfg n).inputSymbol (cfg n).workTapeSymbols = true →
      ∃ u, (loopRound tm mark).runFrom ((cfg n).withState (some (loopRound tm mark).q₀)) u =
        (cfg (n + 1)).withState none := by
    intro n _
    obtain ⟨tn, sn, hn⟩ := hstep (n + 1)
    obtain ⟨ws', e', hrun, ⟨hws', he'⟩, -⟩ := transformsTapes_iff_runFrom.mp
      (transformsTapes_loopRound mark (vp := w n) hn) (w 0) (words (w n) (w (n + 1))) [] rfl
    rw [hws', he', List.nil_append] at hrun
    exact ⟨_, hrun⟩
  have hwhileDiv : ∀ u, ¬((whileCond (nextNonEmpty k Symbol) (loopRound tm mark)).runFrom
      ((cfg 0).withState (some (.inr ()))) u).Halted := by
    intro u hu
    obtain ⟨n, -, hfalse, -⟩ := (whileCond_halted_run_iff (c := nextNonEmpty k Symbol)
      (tm := loopRound tm mark) cfg hbody _).mp ⟨hu, u, rfl⟩
    exact Bool.noConfusion ((hcond n).symm.trans hfalse)
  rw [loopMachine, initCfg_seq_eq_wordsCfg] at hhalt
  refine not_halted_seq_of_right hloadRun rfl (fun u => ?_) t hhalt
  exact not_halted_seq_of_right hfirstRun rfl (not_halted_seq_of_left hwhileDiv) u

private theorem not_halts_extendTapes {k' : ℕ} {tm : MultiTapeTM k Symbol State}
    (e : Fin k ↪ Fin k') {x : List Symbol} (h : ¬tm.Halts x) :
    ¬(tm.extendTapes e).Halts x := by
  rintro ⟨t, hhalt⟩
  refine h ⟨t, ?_⟩
  have hinit : (tm.extendTapes e).initCfg x =
      embed e (tm.initCfg x) (fun _ _ => none) (fun _ => 0) :=
    (embed_eq_of_forall_embed e (tm.initCfg x) (fun _ => rfl) (fun _ => rfl)).symm
  rwa [hinit, ← embedHom_apply tm, runFrom_map, embedHom_apply] at hhalt

private theorem not_halted_outputToTape {tm : MultiTapeTM k Symbol State}
    {x : List Symbol} (h : ¬tm.Halts x) (t : ℕ) :
    ¬(tm.outputToTape.runFrom (tm.outputToTape.initCfg x) t).Halted := by
  intro hhalt
  refine h ⟨t, ?_⟩
  rwa [initCfg_outputToTape, ← outCfgHom_apply tm, runFrom_map, outCfgHom_apply] at hhalt

private theorem not_halts_comp_of_left {k₁ k₂ : ℕ} {S₁ S₂ : Type*}
    {tm₁ : MultiTapeTM k₁ Symbol S₁} {tm₂ : MultiTapeTM k₂ Symbol S₂}
    {x : List Symbol} (h₁ : ¬tm₁.Halts x) (mark : Symbol) :
    ¬(tm₂.comp tm₁ mark).Halts x := by
  rintro ⟨t, hhalt⟩
  have h1 : ¬(tm₁.extendTapes (Fin.castLEEmb (le_max_left k₁ k₂))).Halts x :=
    not_halts_extendTapes _ h₁
  have h2 : ∀ u, ¬((tm₁.extendTapes (Fin.castLEEmb (le_max_left k₁ k₂))).outputToWord.runFrom
      ((tm₁.extendTapes (Fin.castLEEmb (le_max_left k₁ k₂))).outputToWord.initCfg x) u).Halted :=
    fun u => not_halted_seq_of_left (not_halted_outputToTape h1) u
  have h3 : ∀ u, ¬(((tm₁.extendTapes (Fin.castLEEmb (le_max_left k₁ k₂))).outputToWord.extendTapes
      Fin.castSuccEmb).runFrom
        (((tm₁.extendTapes (Fin.castLEEmb (le_max_left k₁ k₂))).outputToWord.extendTapes
          Fin.castSuccEmb).initCfg x) u).Halted := fun u hu =>
    not_halts_extendTapes Fin.castSuccEmb (fun ⟨v, hv⟩ => h2 v hv) ⟨u, hu⟩
  exact not_halted_seq_of_left h3 t hhalt

private theorem not_halts_comp_of_right {k₁ k₂ : ℕ} {S₁ S₂ : Type*}
    {tm₁ : MultiTapeTM k₁ Symbol S₁} {tm₂ : MultiTapeTM k₂ Symbol S₂}
    {x w : List Symbol} {t₁ s₁ : ℕ}
    (h₁ : tm₁.ComputesTidilyInTimeAndSpace x w t₁ s₁) (h₂ : ¬tm₂.Halts w) (mark : Symbol) :
    ¬(tm₂.comp tm₁ mark).Halts x := by
  rintro ⟨t, hhalt⟩
  set K := max k₁ k₂
  set A : Fin (K + 2) := Fin.natAdd K 0
  have hA : Fin.append (fun _ : Fin K => ([] : List Symbol)) ![w, []] =
      Function.update (fun _ => []) A w := by
    simpa only [A] using (append_nil_eq_update (k := K) w)
  obtain ⟨ws₁, e₁, hp₁Run, ⟨hws₁, he₁⟩, -⟩ :=
    transformsTapes_iff_runFrom.mp
      ((h₁.extendTapes (Fin.castLEEmb (le_max_left k₁ k₂))).outputToWord_onTape
        (show Fin.castSuccEmb (Fin.last K) = A by simp [A, Fin.ext_iff]))
      x (fun _ => []) [] ⟨rfl, rfl⟩
  rw [hws₁, he₁, List.nil_append] at hp₁Run
  have hflag : ∃ u, (markFlag K (some mark)).runFrom
      (wordsCfg x (some (markFlag K (some mark)).q₀) (Function.update (fun _ => []) A w) []) u =
      inCfg mark (wordsCfg w (none : Option MarkWorkState) (fun _ : Fin K => []) []) x := by
    have hrun := runFrom_markWork (Symbol := Symbol) (input := x) (some mark) 1 (tapeOfList []) [] 0
    refine ⟨2, ?_⟩
    rw [markFlag, extendTapes_q₀, runFrom_tapeEmb]
    have hone : oneTapeCfg (Fin.natAdd K 1)
        (wordsCfg x (some (markWork Symbol (some mark)).q₀)
          (Function.update (fun _ => []) A w) []) =
        ⟨some (markWork Symbol (some mark)).q₀, 1, fun _ => tapeOfList [], fun _ => 0, []⟩ := by
      have hne : Fin.natAdd K 1 ≠ A := by simp [A, Fin.ext_iff]
      simp [oneTapeCfg, wordsCfg, Function.update_of_ne hne]
    rw [hone, hrun, embed_tapeEmb, ← hA, wordsCfg_append_words, inCfg_wordsCfg]
    refine Cfg.ext rfl rfl ?_ ?_ rfl
    · simpa using update_append_flag (fun _ : Fin K => tapeOfList ([] : List Symbol))
        (tapeOfList w) (tapeOfList []) (Function.update (fun _ => none) (-1) (some mark))
    · funext l; simp [Function.update_apply]
  obtain ⟨uFlag, huFlag⟩ := hflag
  have h2ext : ¬(tm₂.extendTapes (Fin.castLEEmb (le_max_right k₁ k₂))).Halts w :=
    not_halts_extendTapes _ h₂
  let tm2e := tm₂.extendTapes (Fin.castLEEmb (le_max_right k₁ k₂))
  have hinpDiv : ∀ u, ¬(tm2e.inputFromTape.runFrom
      ((inCfg mark (wordsCfg w (none : Option MarkWorkState) (fun _ : Fin K => []) []) x).withState
        (some tm2e.inputFromTape.q₀)) u).Halted := by
    intro u hu
    refine h2ext ⟨u, ?_⟩
    have hstart : (inCfg mark (wordsCfg w (none : Option MarkWorkState)
        (fun _ : Fin K => []) []) x).withState (some tm2e.inputFromTape.q₀) =
        inCfg mark (tm2e.initCfg w) x := by
      refine Cfg.ext rfl rfl (funext fun l => ?_) (funext fun l => ?_) rfl
      · induction l using Fin.addCases <;>
          simp [K, Cfg.withState, inCfg, wordsCfg, Cfg.init, MultiTapeNTM.initCfg, tapeOfList_nil]
      · induction l using Fin.addCases <;>
          simp [K, Cfg.withState, inCfg, wordsCfg, Cfg.init, MultiTapeNTM.initCfg]
    rwa [hstart, ← inCfgHom_apply, runFrom_map, inCfgHom_apply] at hu
  rw [MultiTapeTM.comp, initCfg_seq_eq_wordsCfg] at hhalt
  refine not_halted_seq_of_right hp₁Run rfl (fun u => ?_) t hhalt
  refine not_halted_seq_of_left
    (cfg := wordsCfg x (some (tm2e.inputFromWord mark).q₀) (Function.update (fun _ => []) A w) [])
    (fun v => ?_) u
  exact not_halted_seq_of_right huFlag rfl (not_halted_seq_of_left hinpDiv) v

end Machinery

/-- **Partial iteration of a polynomial-time step until the empty encoding.** Given polynomial-time
`init`, `step`, and `fin`, there is one fixed binary multi-tape Turing machine `tm` with finitely
many states and fixed constants `c, d` such that for every input `a`:
* if `r` is the least round with `encState (step^[r + 1] (init a)) = []`, and every intermediate
  state up to round `r` has encoded length at most `l`, then `tm` halts on `encIn a` with output
  `encOut (fin (step^[r] (init a)))` within time `c * (r + 1) * (l + (encIn a).length + 1) ^ d`
  and space `c * (l + (encIn a).length + 1) ^ d`;
* if `encState (step^[n + 1] (init a)) ≠ []` for every `n`, then `tm` diverges on `encIn a`. -/
theorem exists_partial_iterateWhile {α β γ : Type}
    {encIn : α ↪ List Bool} {encState : β ↪ List Bool} {encOut : γ ↪ List Bool}
    {init : α → β} {step : β → β} {fin : β → γ}
    (hinit : ComputableInPolyTime init encIn encState)
    (hstep : ComputableInPolyTime step encState encState)
    (hfin : ComputableInPolyTime fin encState encOut) :
    ∃ (k : ℕ) (State : Type) (_ : Finite State) (tm : MultiTapeTM k Bool State) (c d : ℕ),
      (∀ (a : α) (r l : ℕ),
        (∀ n ≤ r, (encState (step^[n] (init a))).length ≤ l) →
        (∀ n < r, encState (step^[n + 1] (init a)) ≠ []) →
        encState (step^[r + 1] (init a)) = [] →
        tm.ComputesInTimeAndSpace (encIn a) (encOut (fin (step^[r] (init a))))
          (c * (r + 1) * (l + (encIn a).length + 1) ^ d)
          (c * (l + (encIn a).length + 1) ^ d)) ∧
      (∀ a : α, (∀ n, encState (step^[n + 1] (init a)) ≠ []) → ¬tm.Halts (encIn a)) := by
  obtain ⟨ci, di, ki, Si, _, tmi, hi⟩ := Internal.NormalForm.polyTime hinit
  obtain ⟨cs, ds, ks, Ss, _, tms, hs⟩ := Internal.NormalForm.polyTime hstep
  obtain ⟨cf, df, kf, Sf, _, tmf, hf⟩ := Internal.NormalForm.polyTime hfin
  let main := (loopMachine tms true).comp tmi true
  let kMain := max ki (ks + 1 + 2) + 2
  let c₀ := 6 * max kMain kf + 29
  let E := 2 * (ks + 3) + 1
  let D := 2 * di + 2 * ds + 2 * df + 1
  let C := 2 * ci + cs + E * cs + 2 * cf + 2 * c₀ + 6 * ki + E * (6 * ks + 54) + 10 * ks + 200
  refine ⟨_, _, ?_, tmf.comp main true, C, D, ?_, ?_⟩
  · repeat apply Finite.instSum
  · intro a r l hl hne hnil
    have hloop := computesTidily_loopMachine (tm := tms)
      (w := fun n => encState (step^[n] (init a))) (r := r)
      (t := cs * (l + 1) ^ ds) (s := cs * (l + 1) ^ ds) (l := l)
      (fun n hn => by
        let bound :=
          Nat.mul_le_mul_left cs (Nat.pow_le_pow_left (Nat.add_le_add_right (hl n hn) 1) ds)
        simpa only [Function.iterate_succ_apply'] using (hs (step^[n] (init a))).mono bound bound)
      hl hne hnil true
    have hmain := (hi a).comp hloop true
    have hraw := hmain.comp (hf (step^[r] (init a))) true
    have hpow {e x : ℕ} (he : e ≤ D) (hx : x + 1 ≤ l + (encIn a).length + 1) :
        (x + 1) ^ e ≤ (l + (encIn a).length + 1) ^ D :=
      (Nat.pow_le_pow_left hx e).trans (Nat.pow_le_pow_right (by omega) he)
    have h1 : ci * ((encIn a).length + 1) ^ di ≤ ci * (l + (encIn a).length + 1) ^ D :=
      Nat.mul_le_mul_left ci (hpow (by omega) (by omega))
    have h3 : cs * (l + 1) ^ ds ≤ cs * (l + (encIn a).length + 1) ^ D :=
      Nat.mul_le_mul_left cs (hpow (by omega) (by omega))
    have hlast := hl r le_rfl
    have h5 : cf * ((encState (step^[r] (init a))).length + 1) ^ df ≤
        cf * (l + (encIn a).length + 1) ^ D :=
      Nat.mul_le_mul_left cf (hpow (by omega) (by omega))
    have hlP : l + 1 ≤ (l + (encIn a).length + 1) ^ D := by
      simpa only [pow_one] using hpow (show 1 ≤ D by omega) (x := l) (by omega)
    have hfirst := hl 0 (Nat.zero_le r)
    have hmax : max ki (ks + 1 + 2) ≤ ki + ks + 3 := by omega
    have hPpos : 1 ≤ (l + (encIn a).length + 1) ^ D := Nat.one_le_pow _ _ (by omega)
    have ho2 : 5 * (encState (step^[r] (init a))).length +
        (6 * max (max ki (ks + 1 + 2) + 2) kf + 20) ≤
        c₀ * ((encState (step^[r] (init a))).length + 1) := by
      have hm := Nat.mul_le_mul_right (encState (step^[r] (init a))).length
        (show 5 ≤ c₀ by dsimp only [c₀]; omega)
      dsimp only [c₀, kMain] at hm ⊢
      rw [Nat.mul_add, Nat.mul_one]
      omega
    refine (hraw.mono ?_ ?_).computesInTimeAndSpace
    · set P := (l + (encIn a).length + 1) ^ D
      have hloopT : cs * (l + 1) ^ ds + 10 * l + 24 ≤ (cs + 34) * P := by nlinarith
      have hmid : (r + 1) * (cs * (l + 1) ^ ds + 10 * l + 24) ≤ (r + 1) * ((cs + 34) * P) :=
        Nat.mul_le_mul_left (r + 1) hloopT
      have hrest : ci * ((encIn a).length + 1) ^ di + (8 * l + 18) +
          4 * (encState (init a)).length + 9 +
          cf * ((encState (step^[r] (init a))).length + 1) ^ df +
          4 * (encState (step^[r] (init a))).length + 9 ≤ (ci + cf + 52) * P := by
        simp only [Function.iterate_zero, id_eq] at hfirst
        nlinarith
      have hrest' : (ci + cf + 52) * P ≤ (r + 1) * ((ci + cf + 52) * P) :=
        Nat.le_mul_of_pos_left _ (Nat.succ_pos r)
      have hsum : (r + 1) * ((cs + 34) * P) + (r + 1) * ((ci + cf + 52) * P) ≤
          C * (r + 1) * P := by
        rw [← Nat.mul_add, ← Nat.add_mul, ← mul_assoc (r + 1), mul_comm (r + 1)]
        exact Nat.mul_le_mul_right P (Nat.mul_le_mul_right (r + 1) (by dsimp only [C]; omega))
      simp only [Function.iterate_zero, id_eq] at hfirst ⊢
      omega
    · set P := (l + (encIn a).length + 1) ^ D
      have hY : cs * (l + 1) ^ ds + 10 * l + 6 * ks + 44 ≤ (cs + 6 * ks + 54) * P := by
        have : 6 * ks + 44 ≤ (6 * ks + 44) * P := Nat.le_mul_of_pos_right _ hPpos
        nlinarith
      have hEY : E * (cs * (l + 1) ^ ds + 10 * l + 6 * ks + 44) ≤
          E * ((cs + 6 * ks + 54) * P) := Nat.mul_le_mul_left E hY
      have ho2' : 5 * (encState (step^[r] (init a))).length +
          (6 * max (max ki (ks + 1 + 2) + 2) kf + 20) ≤ c₀ * P :=
        ho2.trans (Nat.mul_le_mul_left c₀ (by omega))
      have hconst : 6 * ki + 10 * ks + 94 ≤ (6 * ki + 10 * ks + 94) * P :=
        Nat.le_mul_of_pos_right _ hPpos
      simp only [Function.iterate_zero, id_eq] at hfirst
      dsimp only [C, E] at hEY ⊢
      nlinarith
  · intro a hne
    have hiterDiv : ¬(loopMachine tms true).Halts (encState (init a)) :=
      not_halts_loopMachine (w := fun n => encState (step^[n] (init a)))
        (fun n => ⟨_, _, by simpa only [Function.iterate_succ_apply'] using hs (step^[n] (init a))⟩)
        hne true
    exact not_halts_comp_of_left (not_halts_comp_of_right (hi a) hiterDiv true) true

end Turing.MultiTapeTM
