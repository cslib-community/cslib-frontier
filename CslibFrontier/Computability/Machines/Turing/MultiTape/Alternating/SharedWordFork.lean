/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.SharedFork
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.TwoWordLoad
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.WorkTapePredicate

/-!
# A shared word for two independently compiled machines

Each child receives the designated tape at the same cursor, even when their tape counts and
designated tape numbers differ. A universal state checks both child verdicts in one extra step.
-/

public section

namespace Turing.MultiTapeATM.SharedWordFork

open MultiTapeTM TwoWordLoad

/-- The candidate remains on its work tape at the given cursor. -/
@[expose] def start {K : ℕ} {S : Type} (src : Fin K) (atm : MultiTapeATM K Bool S)
    (input word : List Bool) (pos : ℕ) :=
  WordGameLeaf.config src (some atm.toPTM.initial) word pos (blank K input)

/-- A shared word at the native predicate's designated input tape is its actual initial
work-tape configuration, including the host input head and blank scratch and marker tapes. -/
theorem start_eq_workTape {k : ℕ} {S : Type} (atm : MultiTapeATM (k + 2) Bool S)
    (input word : List Bool) :
    start (Fin.natAdd k 0) atm input word 0 =
      (WorkTapePredicate.config input word).withState (some atm.toPTM.initial) := by
  apply Cfg.ext <;> try rfl
  · funext i z
    by_cases hi : i = Fin.natAdd k 0 <;>
      simp [start, WordGameLeaf.config, blank, WorkTapePredicate.config, tapesCfg, hi]
  · funext i
    simp [start, WordGameLeaf.config, blank, WorkTapePredicate.config, tapesCfg]

private theorem view_start {k K : ℕ} {S : Type} (atm : MultiTapeATM k Bool S)
    (emb : Fin k ↪ Fin K) (src : Fin k) (input word : List Bool) (pos : ℕ) :
    viewCfg emb (start (emb src) (atm.extendTapes emb) input word pos) =
      start src atm input word pos := by
  apply Cfg.ext <;> try rfl
  · funext i z
    by_cases hi : i = src
    · subst i
      simp [start, viewCfg, WordGameLeaf.config]
    · simp [start, viewCfg, WordGameLeaf.config, hi, emb.injective.ne hi, blank, tapesCfg]
  · funext i
    by_cases hi : i = src
    · subst i
      simp [start, viewCfg, WordGameLeaf.config]
    · simp [start, viewCfg, WordGameLeaf.config, hi, emb.injective.ne hi, blank, tapesCfg]

/-- Place both child machines on a single physical shared word, with all private work tapes
blank. The universal fork costs one extra step on all paths. -/
theorem exists_both {I J : ℕ} {L R : Type} [Finite L] [Finite R]
    (i : Fin I) (left : MultiTapeATM I Bool L) (j : Fin J) (right : MultiTapeATM J Bool R) :
    ∃ (K : ℕ) (src : Fin K) (Q : Type) (_ : Finite Q) (atm : MultiTapeATM K Bool Q),
      ∀ (input word : List Bool) (pos t : ℕ),
        let ca := start i left input word pos
        let cb := start j right input word pos
        let cfg := start src atm input word pos
        left.HaltsWithin t ca → right.HaltsWithin t cb →
          atm.HaltsWithin (t + 1) cfg ∧ (atm.AcceptsWithin (t + 1) cfg ↔
            left.AcceptsWithin t ca ∧ right.AcceptsWithin t cb) := by
  classical
  let K := max I J + 1
  let src : Fin K := Fin.last (max I J)
  let embed {n : ℕ} (h : n ≤ max I J) (slot : Fin n) : Fin n ↪ Fin K :=
    let e := (Fin.castLEEmb h).trans Fin.castSuccEmb
    e.trans (Equiv.swap (e slot) src).toEmbedding
  let eL := embed (Nat.le_max_left I J) i
  let eR := embed (Nat.le_max_right I J) j
  have hi : eL i = src := by simp [eL, embed]
  have hj : eR j = src := by simp [eR, embed]
  let S : Bool → Type | false => L | true => R
  let family : (b : Bool) → MultiTapeATM K Bool (S b)
    | false => left.extendTapes eL
    | true => right.extendTapes eR
  let (b : Bool) : Finite (S b) := by cases b <;> assumption
  refine ⟨K, src, _, inferInstance, SharedFork.machine family, ?_⟩
  intro input word pos t
  dsimp only
  intro ha hb
  let c := WordGameLeaf.config src (none : Option Unit) word pos (blank K input)
  have hl : viewCfg eL (c.withState (some (family false).toPTM.initial)) =
      start i left input word pos := by
    simpa only [hi, c, family, start, WordGameLeaf.config, Cfg.withState] using
      view_start left eL i input word pos
  have hr : viewCfg eR (c.withState (some (family true).toPTM.initial)) =
      start j right input word pos := by
    simpa only [hj, c, family, start, WordGameLeaf.config, Cfg.withState] using
      view_start right eR j input word pos
  have hh := SharedFork.spec family c t (by
    rintro (_ | _)
    · exact (left.haltsWithin_extendTapes_iff eL t _).2 (hl ▸ ha)
    · exact (right.haltsWithin_extendTapes_iff eR t _).2 (hr ▸ hb))
  refine ⟨hh.1, hh.2.trans ?_⟩
  rw [Bool.forall_bool]
  exact and_congr ((left.acceptsWithin_extendTapes_iff eL t _).trans (hl ▸ Iff.rfl))
    ((right.acceptsWithin_extendTapes_iff eR t _).trans (hr ▸ Iff.rfl))

end Turing.MultiTapeATM.SharedWordFork
