/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.NondeterministicQueryMachine.Native

/-!
# Common windows for all native query-loop prefixes

The bounds here concern every native path, with no bound on its length. Each deterministic
routine starts with its heads at the common origin. Its space bound therefore confines its
heads to the same window as every other invocation. The choice and continuation instructions
move no heads. Repeating the routines does not multiply the window by the number of iterations.

## Main results

* `Turing.NondeterministicQueryMachine.Native.head_drop_check`: the suffix after a check
  starts at the deterministic continuation boundary.
* `Turing.NondeterministicQueryMachine.Native.choose_inWindow`: every prefix from a pass boundary
  stays in the common routine window, assuming a preserved invariant on tape words.
-/

public section

namespace Turing.NondeterministicQueryMachine.Native

variable {k : ℕ} {SI SF : Type} {SP : Bool → Type}
  (I : MultiTapeTM k Bool SI) (P : (b : Bool) → MultiTapeTM k Bool (SP b))
  (F : MultiTapeTM k Bool SF) (C : Fin k)

/-- From a word-holding configuration the continuation instruction reads exactly whether the
continuation word is empty. -/
theorem step_check_words {input : List Bool} (choice : Bool)
    (ws : Fin k → List Bool) (out : List Bool) :
    ((table I P F C).withCoin choice).toTM.step (wordsCfg input (some .check) ws out) =
      wordsCfg input (some (if ws C = [] then .finish F.q₀ else .choose)) ws out := by
  rw [step_check I P F C choice _ rfl]
  cases hc : ws C <;> simp [Cfg.workTapeSymbols, wordsCfg, tapeOfList_zero, Cfg.withState, hc]

/-- The suffix immediately after a check takes its deterministic continuation route.
The checked word selects the finalizer or choice boundary without changing tapes or output. -/
theorem head_drop_check {input : List Bool} (p : (machine I P F C).RunPath input)
    (i : Fin p.length) {ws : Fin k → List Bool} {out : List Bool}
    (hcheck : p i.castSucc = wordsCfg input (some .check) ws out) :
    (p.drop i.succ).head =
      wordsCfg input (some (if ws C = [] then .finish F.q₀ else .choose)) ws out := by
  have hstep : (machine I P F C).Step (p i.castSucc) (p i.succ) := p.step i
  obtain ⟨coin, hcoin⟩ := (step_iff I P F C).mp (hcheck ▸ hstep)
  rw [step_check_words I P F C coin] at hcoin
  simpa only [RelSeries.head_drop] using hcoin.symm

/-- A path headed by a word-holding configuration has its work heads at the origin. -/
private theorem head_mem_window {input : List Bool} {p : (machine I P F C).RunPath input}
    {q ws out} {s : ℕ} (hhead : p.head = wordsCfg input q ws out) (i : Fin k) :
    p.head.workTapePos i ∈ window s := by
  simp [hhead, mem_window]

/-- A path stays in a window when its configurations before `cut` and its suffix from `cut` do. -/
private theorem inWindow_of_drop {k' : ℕ} {S : Type} {ntm : MultiTapeNTM k' Bool S}
    {input : List Bool} (p : ntm.RunPath input) (cut : Fin (p.length + 1)) {s : ℕ}
    (hpre : ∀ j : Fin (p.length + 1), j.val < cut.val → ∀ i, (p j).workTapePos i ∈ window s)
    (htail : MultiTapeNTM.RunPath.InWindow (p.drop cut) s) : p.InWindow s := by
  rintro _ ⟨j, rfl⟩ i
  by_cases hj : j.val < cut.val
  · exact hpre j hj i
  · have hindex : j.val - cut.val < (p.drop cut).length + 1 := by
      simp only [RelSeries.drop_length]; omega
    simpa [RelSeries.drop, Nat.sub_add_cancel (Nat.not_lt.mp hj)] using
      htail _ ⟨⟨j.val - cut.val, hindex⟩, rfl⟩ i

/-- Any prefix begun at a finalizer stays in its deterministic window, including arbitrary
halted self-loop padding after the finalizer ends. -/
theorem finish_inWindow {input : List Bool} {ws : Fin k → List Bool} {out : List Bool}
    {t s : ℕ}
    (hF : MultiTapeTM.TransformsTapes F
      (fun inp w => inp = input ∧ w = ws) (fun _ _ _ _ => True) t s)
    (p : (machine I P F C).RunPath input)
    (hhead : p.head = wordsCfg input (some (.finish F.q₀)) ws out) : p.InWindow s := by
  obtain ⟨ws', e, _, q₀, hqhead, hqlast, _, hspace⟩ := hF input ws out ⟨rfl, rfl⟩
  obtain ⟨q, hhead', hlast', _, hmem⟩ := q₀.exists_running (by rw [hqlast]; rfl)
  have hmap : p.head = q.head.mapState finishState :=
    hhead.trans (by simp [hhead', hqhead, mapState_wordsCfg, finishState])
  have hwin := MultiTapeNTM.RunPath.inWindow_of_space_le (p := q₀)
    (by simp [hqhead]) hspace
  rintro _ ⟨n, rfl⟩ i
  by_cases hn : n.val ≤ q.length
  · rw [follows_finish I P F C p q hmap n n.isLt (by omega)]
    exact hwin _ (hmem _ ⟨_, rfl⟩) i
  · have hq : q.length < p.length + 1 := by omega
    have hfinal : p ⟨q.length, hq⟩ = wordsCfg input none ws' (out ++ e) := by
      have h : p ⟨q.length, hq⟩ = q.last.mapState finishState :=
        follows_finish I P F C p q hmap q.length hq (Nat.lt_succ_self _)
      simpa [hlast', hqlast, finishState] using h
    have hhalt : (p ⟨q.length, hq⟩).Halted := by rw [hfinal]; rfl
    have heq : p n = p ⟨q.length, hq⟩ :=
      MultiTapeNTM.RunPath.last_eq_of_halted (p.take n)
        ⟨q.length, by simp only [RelSeries.take]; omega⟩
        (show ((p.take n) ⟨q.length, by simp only [RelSeries.take]; omega⟩).Halted from hhalt)
    simp [heq, hfinal, mem_window]

/-- **Every native pass-loop prefix stays in one fixed window.** Each of the two pass routines
preserves `Inv` on tape words and uses at most `s` cells when started at the origin. The finalizer
has the same bound. These routines can run arbitrarily many times: the conclusion is independent
of the number of passes and applies to all native choices and all computation prefixes. -/
theorem choose_inWindow {input : List Bool} (Inv : (Fin k → List Bool) → Prop) {s : ℕ}
    (hP : ∀ b ws, Inv ws → ∃ t, MultiTapeTM.TransformsTapes (P b)
      (fun inp w => inp = input ∧ w = ws) (fun _ _ w' _ => Inv w') t s)
    (hF : ∀ ws, Inv ws → ∃ t, MultiTapeTM.TransformsTapes F
      (fun inp w => inp = input ∧ w = ws) (fun _ _ _ _ => True) t s)
    (p : (machine I P F C).RunPath input) {ws : Fin k → List Bool} {out : List Bool}
    (hInv : Inv ws) (hhead : p.head = wordsCfg input (some .choose) ws out) : p.InWindow s := by
  have aux : ∀ n, ∀ p : (machine I P F C).RunPath input, p.length = n →
      ∀ ws out, Inv ws → p.head = wordsCfg input (some .choose) ws out → p.InWindow s := by
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro p hlen ws out hInv hhead
      by_cases hzero : p.length = 0
      · rintro _ ⟨j, rfl⟩ i
        obtain rfl : j = 0 := by omega
        exact head_mem_window I P F C hhead i
      have hone : 1 < p.length + 1 := by omega
      have hfirst : (machine I P F C).Step p.head (p ⟨1, hone⟩) := p.step ⟨0, by omega⟩
      obtain ⟨b, hb⟩ := (step_iff I P F C).mp (hhead ▸ hfirst)
      rw [step_choose I P F C b _ rfl, withState_wordsCfg] at hb
      let p₁ := p.drop ⟨1, hone⟩
      obtain ⟨t, ht⟩ := hP b ws hInv
      obtain ⟨ws', e, hInv', q₀, hqhead, hqlast, _, hspace⟩ := ht input ws out ⟨rfl, rfl⟩
      obtain ⟨q, hhead', hlast', _, hmem⟩ := q₀.exists_running (by rw [hqlast]; rfl)
      have hmap : p₁.head = q.head.mapState (passState b) := by
        rw [hhead', hqhead, mapState_wordsCfg]
        exact hb.symm
      have hwin := MultiTapeNTM.RunPath.inWindow_of_space_le (p := q₀)
        (by simp [hqhead]) hspace
      have hbefore (j : ℕ) (hj : j < p.length + 1) (hj' : j ≤ q.length + 1) :
          ∀ i, (p ⟨j, hj⟩).workTapePos i ∈ window s := by
        cases j with
        | zero => exact head_mem_window I P F C hhead
        | succ j =>
          have heq : p ⟨j + 1, hj⟩ = _ := follows_pass I P F C b p₁ q hmap j
            (by simp only [p₁, RelSeries.drop_length]; omega) (Nat.lt_of_succ_le hj')
          intro i
          rw [heq]
          exact hwin _ (hmem _ ⟨_, rfl⟩) i
      by_cases hshort : p.length ≤ q.length + 1
      · rintro _ ⟨j, rfl⟩ i
        exact hbefore j j.isLt (by omega) i
      have hcheck : q.length + 1 < p.length := by omega
      have hcfg : p ⟨q.length + 1, by omega⟩ =
          wordsCfg input (some .check) ws' (out ++ e) := by
        have heq : p ⟨q.length + 1, by omega⟩ = q.last.mapState (passState b) :=
          follows_pass I P F C b p₁ q hmap q.length
            (by simp only [p₁, RelSeries.drop_length]; omega) (Nat.lt_succ_self _)
        simpa [hlast', hqlast, passState] using heq
      have hnext := head_drop_check I P F C p ⟨q.length + 1, hcheck⟩ hcfg
      let cut : Fin (p.length + 1) := ⟨q.length + 2, by omega⟩
      have htail : MultiTapeNTM.RunPath.InWindow (p.drop cut) s := by
        by_cases hblank : ws' C = []
        · obtain ⟨tF, htF⟩ := hF ws' hInv'
          apply finish_inWindow I P F C htF
          simpa [cut, hblank] using hnext
        · apply ih (p.drop cut).length
            (by simp only [RelSeries.drop_length, cut, hlen]; omega) (p.drop cut) rfl
            ws' (out ++ e) hInv'
          simpa [cut, hblank] using hnext
      exact inWindow_of_drop p cut
        (fun j hj i => hbefore j j.isLt (by dsimp [cut] at hj; omega) i) htail
  exact aux p.length p rfl ws out hInv hhead

/-- The initial continuation check either enters the finalizer or the choice loop without
moving any tape head, so it preserves their common workspace window. -/
private theorem check_inWindow {input : List Bool} (Inv : (Fin k → List Bool) → Prop) {s : ℕ}
    (hP : ∀ b ws, Inv ws → ∃ t, MultiTapeTM.TransformsTapes (P b)
      (fun inp w => inp = input ∧ w = ws) (fun _ _ w' _ => Inv w') t s)
    (hF : ∀ ws, Inv ws → ∃ t, MultiTapeTM.TransformsTapes F
      (fun inp w => inp = input ∧ w = ws) (fun _ _ _ _ => True) t s)
    (p : (machine I P F C).RunPath input) {ws : Fin k → List Bool} {out : List Bool}
    (hInv : Inv ws) (hhead : p.head = wordsCfg input (some .check) ws out) : p.InWindow s := by
  by_cases hzero : p.length = 0
  · rintro _ ⟨j, rfl⟩ i
    obtain rfl : j = 0 := by omega
    exact head_mem_window I P F C hhead i
  have hroute := head_drop_check I P F C p ⟨0, by omega⟩ hhead
  have htail : MultiTapeNTM.RunPath.InWindow (p.drop ⟨1, by omega⟩) s := by
    by_cases hblank : ws C = []
    · obtain ⟨tF, htF⟩ := hF ws hInv
      exact finish_inWindow I P F C htF _ (by simpa [hblank] using hroute)
    · exact choose_inWindow I P F C Inv hP hF _ hInv (by simpa [hblank] using hroute)
  refine inWindow_of_drop p ⟨1, by omega⟩ (fun j hj i => ?_) htail
  obtain rfl : j = 0 := Fin.ext (by simpa using hj)
  exact head_mem_window I P F C hhead i

/-- **The complete native loop uses one common window on every computation prefix.** Tidy
initialization establishes the word invariant, the selected passes preserve it, and finalization
terminates tidily. The number of iterations and their runtimes do not occur in the space bound.
This theorem does not assert that the loop terminates. -/
theorem runsInSpace_of_transforms {input : List Bool}
    (Inv : (Fin k → List Bool) → Prop) {s tI : ℕ}
    (hI : MultiTapeTM.TransformsTapes I
      (fun inp ws => inp = input ∧ ws = fun _ => []) (fun _ _ ws' _ => Inv ws') tI s)
    (hP : ∀ b ws, Inv ws → ∃ t, MultiTapeTM.TransformsTapes (P b)
      (fun inp w => inp = input ∧ w = ws) (fun _ _ w' _ => Inv w') t s)
    (hF : ∀ ws, Inv ws → ∃ t, MultiTapeTM.TransformsTapes F
      (fun inp w => inp = input ∧ w = ws) (fun _ _ _ _ => True) t s) :
    (machine I P F C).RunsInSpace input (k * (2 * s + 1)) := by
  intro p
  obtain ⟨ws, e, hInv, q₀, hqhead, hqlast, _, hspace⟩ :=
    hI input (fun _ => []) [] ⟨rfl, rfl⟩
  obtain ⟨q, hhead', hlast', _, hmem⟩ := q₀.exists_running (by rw [hqlast]; rfl)
  have hmap : p.head = q.head.mapState initState := by
    rw [p.head_eq, hhead', hqhead, mapState_wordsCfg]
    change Cfg.init (.init I.q₀ : State SI SP SF) input = _
    simp [initState, wordsCfg]
  have hwin := MultiTapeNTM.RunPath.inWindow_of_space_le (p := q₀)
    (by simp [hqhead]) hspace
  have hpre (j : Fin (p.length + 1)) (hj : j.val ≤ q.length) :
      ∀ i, (p.toRunPath j).workTapePos i ∈ window s := fun i => by
    rw [follows_init I P F C p.toRunPath q hmap j j.isLt (by omega)]
    exact hwin _ (hmem _ ⟨_, rfl⟩) i
  have hpwin : MultiTapeNTM.RunPath.InWindow p.toRunPath s := by
    by_cases hq : q.length < p.length + 1
    · let cut : Fin (p.length + 1) := ⟨q.length, hq⟩
      have hcfg : p.toRunPath cut = wordsCfg input (some .check) ws e := by
        have h : p.toRunPath cut = q.last.mapState initState :=
          follows_init I P F C p.toRunPath q hmap q.length hq (Nat.lt_succ_self _)
        simpa [hlast', hqlast, initState] using h
      exact inWindow_of_drop p.toRunPath cut (fun j hj => hpre j hj.le)
        (check_inWindow I P F C Inv hP hF (p.toRunPath.drop cut) hInv (by simpa using hcfg))
    · rintro _ ⟨j, rfl⟩
      exact hpre j (by omega)
  exact MultiTapeNTM.RunPath.InWindow.space_le hpwin

end Turing.NondeterministicQueryMachine.Native
