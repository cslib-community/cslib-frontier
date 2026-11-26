/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.NondeterministicQueryMachine.Native
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Counting

/-!
# Counting view of the native query loop

The relation-based query-loop compiler samples a bit to specify one of two
transitions. Both values select the same instruction outside a choice state.
For counting, a deterministic step has one occurrence, and a choice boundary
has one occurrence for each bit.

## Main definitions

* `Turing.NondeterministicQueryMachine.Native.countingMachine`: the occurrence-sensitive
  machine with branching only at choice boundaries.
* `Turing.NondeterministicQueryMachine.Native.replayChoices`: replay occurrences and record
  the genuine binary choices.

## Main results

* `Turing.NondeterministicQueryMachine.Native.toNTM_countingMachine`: forgetting occurrence
  labels recovers the original machine and its space bounds.
* `Turing.NondeterministicQueryMachine.Native.eq_occurrences_of_replayChoices`: a first-halting
  branch is determined by the bit sequence at its choice boundaries.
* `Turing.NondeterministicQueryMachine.Native.countingMachine_haltsWithin`: the original
  time bound applies to counted runs.
* `Turing.NondeterministicQueryMachine.Native.branchCount_le_one_of_choiceTrace`: a verdict
  with a unique bit sequence has at most one counted branch.
-/

public section

namespace Turing.NondeterministicQueryMachine.Native

variable {k : ℕ} {SI SF : Type} {SP : Bool → Type}
  (I : MultiTapeTM k Bool SI) (P : (b : Bool) → MultiTapeTM k Bool (SP b))
  (F : MultiTapeTM k Bool SF) (C : Fin k)

private def choiceBits : State SI SP SF → List Bool
  | .choose => [false, true]
  | _ => [false]

/-- Use one transition occurrence per bit at a choice boundary and one occurrence everywhere
else. This preserves deterministic routines when counting branches. -/
noncomputable def countingMachine : MultiTapeCTM k Bool (State SI SP SF) where
  initial := .init I.q₀
  tr q input work _ :=
    (choiceBits q).map fun b =>
      MultiTapeMachine.Action.emptyOracleEquiv.symm (instruction I P F C q input work b)

/-- The counting presentation is nonblocking, even outside the compiler's state invariants. -/
theorem countingMachine_nonblocking : (countingMachine I P F C).Nonblocking := by
  intro q input work
  cases q <;> simp [countingMachine, choiceBits]

/-- Forgetting the occurrence labels recovers the native compiler's reachability relation. -/
theorem toNTM_countingMachine : (countingMachine I P F C).toNTM = machine I P F C := by
  suffices (countingMachine I P F C).toNTM.Tr = (machine I P F C).Tr by
    change MultiTapeNTM.mk _ _ = MultiTapeNTM.mk _ _
    exact congrArg _ this
  ext q input work act
  rw [machine, MultiTapePTM.tr_toNTM_iff]
  simp only [MultiTapeCTM.toNTM, countingMachine, List.mem_map,
    Equiv.apply_symm_apply, Equiv.symm_apply_eq]
  cases q <;> simp [choiceBits, tr_withCoin, instruction]

/-- A bound on the native computation paths is also a clock for the counting presentation. -/
theorem countingMachine_haltsWithin {input : List Bool} {fuel : ℕ}
    (h : (machine I P F C).RunsInTime input fuel) :
    (countingMachine I P F C).HaltsWithin fuel
      (Cfg.init (.init I.q₀) input) := by
  apply MultiTapeCTM.haltsWithin_of_paths (countingMachine_nonblocking I P F C)
  rw [toNTM_countingMachine]
  exact fun p hp hlen => h ⟨p, hp⟩ hlen

private def atChoice {input : List Bool} (cfg : Cfg k Bool (State SI SP SF) input) : Bool :=
  match cfg.state with
  | some .choose => true
  | _ => false

private theorem step_index_lt {input : List Bool}
    {cfg next : Cfg k Bool (State SI SP SF) input} {i : ℕ}
    (h : (countingMachine I P F C).step? cfg i = some next) :
    i < if atChoice cfg then 2 else 1 := by
  obtain ⟨hi, _⟩ := ((countingMachine I P F C).step?_eq_some_iff _ _ _).mp h
  cases hq : cfg.state with
  | none => simp [MultiTapeCTM.actions, hq] at hi
  | some q =>
    cases q <;> simpa [MultiTapeCTM.actions, hq, countingMachine, choiceBits, atChoice] using hi

/-- Replay actual occurrence indices and retain just the bits used at choice boundaries. -/
noncomputable def replayChoices {input : List Bool} :
    Cfg k Bool (State SI SP SF) input → List ℕ →
      Option (List Bool × Cfg k Bool (State SI SP SF) input)
  | cfg, [] => some ([], cfg)
  | cfg, i :: rest => ((countingMachine I P F C).step? cfg i).bind fun next =>
    (replayChoices next rest).map fun (bits, final) =>
      ((if atChoice cfg then (i == 1) :: bits else bits), final)

@[simp]
theorem replayChoices_nil {input : List Bool} (cfg : Cfg k Bool (State SI SP SF) input) :
    replayChoices I P F C cfg [] = some ([], cfg) := by simp only [replayChoices]

/-- The final configuration of the bit-recording replay is the ordinary replay result. -/
theorem map_snd_replayChoices {input : List Bool} (cfg : Cfg k Bool (State SI SP SF) input)
    (indices : List ℕ) :
    (replayChoices I P F C cfg indices).map Prod.snd =
      (countingMachine I P F C).runBranch cfg indices := by
  induction indices generalizing cfg with
  | nil => rfl
  | cons i rest ih =>
    rw [replayChoices, MultiTapeCTM.runBranch_cons]
    cases h : (countingMachine I P F C).step? cfg i with
    | none => rfl
    | some next =>
      simp only [Option.bind, ← ih next]
      rcases replayChoices I P F C next rest with _ | ⟨_, _⟩ <;> rfl

/-- Concatenating occurrence traces concatenates their genuine choice sequences. -/
theorem replayChoices_append {input : List Bool} (cfg : Cfg k Bool (State SI SP SF) input)
    (first second : List ℕ) :
    replayChoices I P F C cfg (first ++ second) =
      (replayChoices I P F C cfg first).bind fun (firstBits, middle) =>
        (replayChoices I P F C middle second).map fun (suffix, final) =>
          (firstBits ++ suffix, final) := by
  induction first generalizing cfg with
  | nil =>
    simp [replayChoices, Option.bind]
  | cons i first ih =>
    simp only [List.cons_append, replayChoices]
    cases (countingMachine I P F C).step? cfg i with
    | none => rfl
    | some next =>
      simp only [Option.bind, ih next]
      rcases replayChoices I P F C next first with _ | ⟨firstBits, middle⟩
      · rfl
      · simp only [Option.map_some, Option.map_map]
        cases atChoice cfg <;> rfl

/-- Crossing a choice boundary adds precisely the bit that selects the next pass. -/
theorem replayChoices_choose {input : List Bool} (cfg : Cfg k Bool (State SI SP SF) input)
    (hcfg : cfg.state = some .choose) (b : Bool) (rest : List ℕ) :
    replayChoices I P F C cfg (b.toNat :: rest) =
      (replayChoices I P F C (cfg.withState (some (.pass b (P b).q₀))) rest).map
        fun (bits, final) => (b :: bits, final) := by
  have hstep : (countingMachine I P F C).step? cfg b.toNat =
      some (cfg.withState (some (.pass b (P b).q₀))) := by
    cases b <;> simp [MultiTapeCTM.step?, MultiTapeCTM.actions, hcfg, countingMachine,
      choiceBits, instruction, apply_routeAction]
  rw [replayChoices, hstep]
  cases b <;> simp [Option.bind, atChoice, hcfg]

/-- A halted replay from a choice boundary must record a genuine choice. -/
theorem replayChoices_choose_ne_nil {input : List Bool}
    {cfg final : Cfg k Bool (State SI SP SF) input} {indices : List ℕ} {bits : List Bool}
    (hcfg : cfg.state = some .choose)
    (hr : replayChoices I P F C cfg indices = some (bits, final))
    (hhalt : final.Halted) : bits ≠ [] := by
  cases indices with
  | nil =>
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj ((replayChoices_nil I P F C cfg).symm.trans hr))
    cases hcfg.symm.trans hhalt
  | cons j indices =>
    rw [replayChoices] at hr
    obtain ⟨_, _, hrest⟩ := Option.bind_eq_some_iff.mp hr
    obtain ⟨⟨_, _⟩, _, heq⟩ := Option.map_eq_some_iff.mp hrest
    rintro rfl
    simp only [atChoice, hcfg, ↓reduceIte, Prod.mk.injEq, reduceCtorEq, false_and] at heq

/-- A live native step outside a choice boundary has one occurrence and records no bit. -/
theorem replayChoices_step_zero {input : List Bool}
    {cfg next : Cfg k Bool (State SI SP SF) input}
    (hstate : cfg.state ≠ some .choose) (hlive : ¬cfg.Halted)
    (hstep : (machine I P F C).Step cfg next) (rest : List ℕ) :
    replayChoices I P F C cfg (0 :: rest) = replayChoices I P F C next rest := by
  have hat : atChoice cfg = false := by
    cases h : cfg.state with
    | none => simp [atChoice, h]
    | some q => cases q <;> simp_all [atChoice]
  rw [← toNTM_countingMachine] at hstep
  obtain ⟨j, hj⟩ := ((countingMachine I P F C).step_toNTM_iff hlive).mp hstep
  obtain rfl : j = 0 := by simpa [hat, Nat.lt_one_iff] using step_index_lt I P F C hj
  rw [replayChoices, hj]
  simp [hat, Option.bind]

/-- A running path through deterministic routines has a replay with no recorded choice bits. -/
theorem replayChoices_replicate_zero {input : List Bool}
    (p : RelSeries ((machine I P F C).runningStepRel input))
    (h : ∀ i : Fin p.length, (p i.castSucc).state ≠ some .choose) :
    replayChoices I P F C p.head (List.replicate p.length 0) = some ([], p.last) := by
  induction p using RelSeries.inductionOn' with
  | singleton cfg => rfl
  | snoc p next hs ih =>
    have hlast : p.last.state ≠ some .choose := by
      change (p (Fin.last p.length)).state ≠ some .choose
      exact (RelSeries.snoc_castSucc p next hs (Fin.last p.length)) ▸
        (h ⟨p.length, by simp⟩ : (p.snoc next hs (Fin.last p.length).castSucc).state ≠ some .choose)
    rw [RelSeries.snoc_length, List.replicate_succ', RelSeries.head_snoc, replayChoices_append,
      ih fun i => (RelSeries.snoc_castSucc p next hs i.castSucc) ▸
        (h ⟨i.val, by simp⟩ : (p.snoc next hs i.castSucc.castSucc).state ≠ some .choose)]
    simpa only [Option.bind, List.nil_append, RelSeries.last_snoc, replayChoices_nil,
      Option.map_some] using
      congrArg (Option.map (fun p => (([] : List Bool) ++ p.1, p.2)))
        (replayChoices_step_zero I P F C hlast hs.1 hs.2 [])


/-- Among successful replays from the same configuration, a shorter replay whose
choice bits are a prefix of the longer replay's bits is an occurrence prefix. -/
theorem prefix_occurrences_of_replayChoices {input : List Bool}
    {cfg final₁ final₂ : Cfg k Bool (State SI SP SF) input} {bits₁ bits₂ : List Bool}
    {indices₁ indices₂ : List ℕ}
    (h₁ : replayChoices I P F C cfg indices₁ = some (bits₁, final₁))
    (h₂ : replayChoices I P F C cfg indices₂ = some (bits₂, final₂))
    (hlen : indices₁.length ≤ indices₂.length) (hprefix : bits₁ <+: bits₂) :
    indices₁ <+: indices₂ := by
  induction indices₁ generalizing cfg bits₁ bits₂ indices₂ with
  | nil => exact List.nil_prefix
  | cons i rest ih =>
    cases indices₂ with
    | nil => simp at hlen
    | cons j tail =>
      simp only [replayChoices, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h₁ h₂
      obtain ⟨x, hx, ⟨bs, f₁⟩, hxs, hbits₁⟩ := h₁
      obtain ⟨y, hy, ⟨cs, f₂⟩, hys, hbits₂⟩ := h₂
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hbits₁
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hbits₂
      have hi := step_index_lt I P F C hx
      have hj := step_index_lt I P F C hy
      obtain ⟨rfl, htail⟩ : i = j ∧ bs <+: cs := by
        cases hc : atChoice cfg
        · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hi hj hprefix
          exact ⟨by omega, hprefix⟩
        · simp only [hc, ↓reduceIte, List.cons_prefix_cons] at hi hj hprefix
          refine ⟨by_contra fun hne => ?_, hprefix.2⟩
          rcases (show (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) by omega) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
            simp at hprefix
      obtain rfl : x = y := Option.some.inj (hx.symm.trans hy)
      obtain ⟨suffix, hs⟩ := ih hxs hys (by simpa using hlen) htail
      exact ⟨suffix, congrArg (i :: ·) hs⟩

/-- A successful replay can be split after any known occurrence prefix whose recorded bits
agree with the corresponding prefix of its trace. -/
theorem exists_suffix_of_replayChoices {input : List Bool}
    {cfg middle final : Cfg k Bool (State SI SP SF) input}
    {first indices : List ℕ} {firstBits lastBits : List Bool}
    (hfirst : replayChoices I P F C cfg first = some (firstBits, middle))
    (hfull : replayChoices I P F C cfg indices = some (firstBits ++ lastBits, final))
    (hlen : first.length ≤ indices.length) :
    ∃ rest, indices = first ++ rest ∧
      replayChoices I P F C middle rest = some (lastBits, final) := by
  obtain ⟨rest, rfl⟩ := prefix_occurrences_of_replayChoices I P F C hfirst hfull hlen
    (List.prefix_append _ _)
  rw [replayChoices_append, hfirst] at hfull
  obtain ⟨⟨bits, cfg'⟩, hrest, heq⟩ := Option.map_eq_some_iff.mp hfull
  obtain ⟨hbits, rfl⟩ := Prod.mk.inj heq
  exact ⟨rest, rfl, List.append_cancel_left hbits ▸ hrest⟩

/-- Two first-halting occurrence traces with the same genuine choice bits coincide. -/
theorem eq_occurrences_of_replayChoices {input : List Bool}
    {cfg final₁ final₂ : Cfg k Bool (State SI SP SF) input} {bits : List Bool}
    {indices₁ indices₂ : List ℕ}
    (h₁ : replayChoices I P F C cfg indices₁ = some (bits, final₁))
    (h₂ : replayChoices I P F C cfg indices₂ = some (bits, final₂))
    (hh₁ : final₁.Halted) (hh₂ : final₂.Halted) : indices₁ = indices₂ := by
  suffices claim : ∀ {a b : List ℕ} {x y : Cfg k Bool (State SI SP SF) input},
      replayChoices I P F C cfg a = some (bits, x) →
      replayChoices I P F C cfg b = some (bits, y) →
      x.Halted → a.length ≤ b.length → a = b by
    rcases Nat.le_total indices₁.length indices₂.length with hl | hl
    · exact claim h₁ h₂ hh₁ hl
    · exact (claim h₂ h₁ hh₂ hl).symm
  intro a b x y ha hb hx hab
  obtain ⟨suffix, rfl⟩ := prefix_occurrences_of_replayChoices I P F C ha hb hab (List.prefix_refl _)
  have hra : (countingMachine I P F C).runBranch cfg a = some x := by
    simpa only [map_snd_replayChoices, Option.map_some] using congrArg (Option.map Prod.snd) ha
  have hrb : (countingMachine I P F C).runBranch cfg (a ++ suffix) = some y := by
    simpa only [map_snd_replayChoices, Option.map_some] using congrArg (Option.map Prod.snd) hb
  rw [MultiTapeCTM.runBranch_append, hra] at hrb
  cases suffix with
  | nil => simp
  | cons j suffix => simp [Option.bind, MultiTapeCTM.runBranch_of_halted _ hx] at hrb

/-- If a verdict determines the genuine choice sequence on every terminal replay, it has
at most one counted branch. -/
theorem branchCount_le_one_of_choiceTrace {input : List Bool}
    (cfg : Cfg k Bool (State SI SP SF) input) (fuel : ℕ) (verdict : List Bool → Bool)
    (bits : List Bool)
    (hbits : ∀ indices trace final, replayChoices I P F C cfg indices = some (trace, final) →
      final.Halted → verdict final.output → trace = bits) :
    (countingMachine I P F C).branchCount verdict fuel cfg ≤ 1 := by
  apply Finset.card_le_one_iff.mpr
  have htrace {indices : List ℕ}
      (h : indices ∈ ((countingMachine I P F C).branches fuel cfg).filter fun is =>
        ((countingMachine I P F C).runBranch cfg is).any fun final => verdict final.output) :
      ∃ final, replayChoices I P F C cfg indices = some (bits, final) ∧ final.Halted := by
    obtain ⟨hmem, hv⟩ := Finset.mem_filter.mp h
    obtain ⟨_, final, hr, hh⟩ := ((countingMachine I P F C).mem_branches_iff _ _ _).mp hmem
    rw [← map_snd_replayChoices] at hr
    obtain ⟨⟨trace, last⟩, ht, rfl⟩ := Option.map_eq_some_iff.mp hr
    have hv' : verdict last.output := by
      simpa [← map_snd_replayChoices, ht] using hv
    obtain rfl := hbits _ _ _ ht hh hv'
    exact ⟨last, ht, hh⟩
  intro first second hfirst hsecond
  obtain ⟨_, hf, hhf⟩ := htrace hfirst
  obtain ⟨_, hs, hhs⟩ := htrace hsecond
  exact eq_occurrences_of_replayChoices I P F C hf hs hhf hhs

end Turing.NondeterministicQueryMachine.Native
