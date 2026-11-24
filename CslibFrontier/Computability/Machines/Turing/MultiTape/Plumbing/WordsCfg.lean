/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate (addition to `Plumbing/WordsCfg.lean`)

public import CslibFrontier.Init
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.WordsCfg
public import Cslib.Foundations.Data.Fin.Tuple
public import Mathlib.Data.Fin.VecNotation

/-!
# Appended tape words in `wordsCfg`

`Turing.wordsCfg_append_words` writes out `Turing.wordsCfg` when the work-tape words end with an
input word `w` and a blank flag tape `[]`, the layout in which virtual-input wrappers start and
halt.
-/

public section

namespace Turing

variable {k : ℕ} {State Symbol : Type*}

/-- A `wordsCfg` configuration whose last two words are `w` and the empty word, written out. -/
lemma wordsCfg_append_words {outer : List Symbol} (q : Option State)
    (ws : Fin k → List Symbol) (w out : List Symbol) :
    wordsCfg outer q (Fin.append ws ![w, []]) out =
      ⟨q, 1, Fin.append (fun j => tapeOfList (ws j)) ![tapeOfList w, fun _ => none],
        fun _ => 0, out⟩ := by
  refine Cfg.ext rfl rfl
    ((Fin.comp_append tapeOfList ws ![w, []]).trans (congrArg _ (funext fun i => ?_))) rfl rfl
  match i with
  | 0 | 1 => simp

end Turing
