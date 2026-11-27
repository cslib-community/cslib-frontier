/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Structured
import Mathlib.Data.List.GetD
import CslibFrontier.Tactic.WramOmega

/-!
# Width-independent native program prefixes

An execution that halts at one width identifies every successful prefix at a larger width when
the program does not read physical width. These rules apply to both complete native frontends
and programs that compose them.

## Main results

* `Code.readsWidth_rename`: register renaming does not change width observation.
* `Runs.prefix_at_smaller_width`: wider prefixes agree with an admitted smaller-width execution.
* `Runs.prefix_bounds`: uniform prefix word bounds and the original outside-memory frame.
* `Runs.prefix_bounds_init`: initialized prefixes also have zero memory above the envelope.

These determinism and representation lemmas are original.
-/

public section

namespace Cslib.WordRAM

/-- Register renaming never changes whether a structured program observes physical width. -/
theorem Code.readsWidth_rename {B : Basis} {r r' : ℕ} (f : Fin r → Fin r')
    (c : Code B r) : (c.rename f).ReadsWidth ↔ c.ReadsWidth := by
  induction c with
  | op o => cases o <;> rfl
  | seq c d hc hd => simp only [Code.rename, Code.ReadsWidth, hc, hd]
  | branch b c d hc hd => simp only [Code.rename, Code.ReadsWidth, hc, hd]
  | loop b c hc => exact hc
  | rand => rfl

/-- Every wider prefix is the same smaller-width prefix if that smaller execution halts. -/
theorem Runs.prefix_at_smaller_width {B : Basis} {w w' r : ℕ} {p : Program B r}
    (hp : ¬p.ReadsWidth) (hw : w ≤ w') {s t : State r} {k v total : ℕ}
    (hwide : Runs w' p s t k) (hlow : Executes w p s v total) : Runs w p s t k := by
  induction hwide using Relation.RelatesInSteps.head_induction_on generalizing total with
  | hrefl => exact .refl _
  | @hhead a c k hstep hrest ih =>
    obtain ⟨z, _ | m, hm, hz, _⟩ := hlow
    · cases hm.zero
      exact absurd ((hstep : step w' p a = .next c).symm.trans (step_halt_mono_width hz))
        (by simp)
    · obtain ⟨u, hu, htail⟩ := hm.succ'
      obtain rfl : u = c := Outcome.next.inj
        ((hstep : step w' p a = .next c).symm.trans (hu.mono_width hp hw)).symm
      exact (ih (total := m + 1) ⟨z, m, htail, hz, rfl⟩).head a u t k hu

/-- A native instruction cannot write memory above the admitted address-word universe. -/
theorem Op.eval_mem_above {B : Basis} {r w a : ℕ} {o : Op B r} {x y : Data r}
    (h : o.eval w x = some y) (hx : x.Bounded w) (ha : 2 ^ w ≤ a) :
    y.mem a = x.mem a := by
  cases o with
  | const => obtain ⟨_, rfl⟩ := Data.put_eq_some.1 h; rfl
  | alu => obtain ⟨_, _, _, rfl⟩ := Op.eval_alu_eq_some.1 h; rfl
  | copy | load =>
    cases h
    rfl
  | store d s =>
    cases h
    exact Function.update_of_ne (by have := hx.1 d; wram_omega [this]) _ _

/-- A complete native step preserves memory beyond the admitted address-word universe. -/
theorem Next.mem_above {B : Basis} {r w a : ℕ} {p : Program B r} {s t : State r}
    (h : Next w p s t) (hs : s.data.Bounded w) (ha : 2 ^ w ≤ a) :
    t.data.mem a = s.data.mem a := by
  unfold Next WordRAM.step at h
  split at h
  · cases h
  · split at h
    · next x hx => cases h; exact Op.eval_mem_above hx hs ha
    · cases h
  all_goals first | (cases h; rfl) | cases h

/-- A native run preserves every cell above its admitted address-word universe. -/
theorem Runs.mem_above {B : Basis} {r w a : ℕ} {p : Program B r} {s t : State r} {n : ℕ}
    (h : Runs w p s t n) (hs : s.data.Bounded w) (ha : 2 ^ w ≤ a) :
    t.data.mem a = s.data.mem a := by
  induction h with
  | refl => rfl
  | @tail t u n hpre hstep ih =>
    exact (hstep.mem_above (Runs.bounded hpre hs) ha).trans ih

/-- A halt at an admitted width bounds every wider prefix and preserves original outside memory.
The envelope bounds the address-word universe; no clearing or initial-zero hypothesis is used. -/
theorem Runs.prefix_bounds {B : Basis} {r w W P v total k : ℕ} {p : Program B r}
    {s₀ s : State r} (hr : Runs W p s₀ s k) (hp : ¬p.ReadsWidth) (hw : w ≤ W)
    (hi : s₀.data.Bounded w) (he : Executes w p s₀ v total) (hP : 2 ^ w ≤ P) :
    (∀ i, s.data.regs i < P) ∧ (∀ a, s.data.mem a < P) ∧
      ∀ a, P ≤ a → s.data.mem a = s₀.data.mem a := by
  have low := hr.prefix_at_smaller_width hp hw he
  have bounded := low.bounded hi
  exact ⟨fun i => (bounded.1 i).trans_le hP, fun a => (bounded.2 a).trans_le hP,
    fun a ha => low.mem_above hi (hP.trans ha)⟩

/-- Initialized wider prefixes have bounded words and zero memory above the same envelope. -/
theorem Runs.prefix_bounds_init {B : Basis} {r w W P v total k : ℕ}
    {p : Program B r} {input : List ℕ} {s : State r}
    (hr : Runs W p (State.init input) s k) (hp : ¬p.ReadsWidth) (hw : w ≤ W)
    (hi : InputFits w input) (he : Executes w p (State.init input) v total) (hP : 2 ^ w ≤ P) :
    (∀ i, s.data.regs i < P) ∧ (∀ a, s.data.mem a < P) ∧
      ∀ a, P ≤ a → s.data.mem a = 0 := by
  obtain ⟨regs, mem, frame⟩ := hr.prefix_bounds hp hw (Data.Bounded.init hi) he hP
  refine ⟨regs, mem, fun a ha => (frame a ha).trans ?_⟩
  rcases a with _ | a
  · exact absurd (Nat.two_pow_pos w) (by omega)
  · exact List.getD_eq_default _ _ <| by
      have hlen := hi.1
      wram_omega [hlen]

end Cslib.WordRAM
