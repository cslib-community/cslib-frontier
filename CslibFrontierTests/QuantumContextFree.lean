/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

import CslibFrontier.Computability.Languages.QuantumContextFree

set_option linter.privateModule false

namespace CslibFrontierTests.QuantumContextFree

open Cslib.Language

private abbrev splitLeft : ContextFreeRule Bool (Fin 3) := ⟨0, [.nonterminal 1]⟩
private abbrev splitRight : ContextFreeRule Bool (Fin 3) := ⟨0, [.nonterminal 2]⟩
private abbrev finishLeft : ContextFreeRule Bool (Fin 3) := ⟨1, [.terminal true]⟩
private abbrev finishRight : ContextFreeRule Bool (Fin 3) := ⟨2, [.terminal true]⟩

private noncomputable abbrev grammar : QuantumContextFreeGrammar Bool where
  grammar := ⟨Fin 3, 0, {splitLeft, splitRight, finishLeft, finishRight}⟩
  finiteNonterminals := inferInstance
  channels := 1
  channels_pos := by decide
  weight _ r := if r.val = splitRight then -1 else 1

private noncomputable abbrev leftTrace : List grammar.grammar.rules :=
  [⟨splitLeft, by decide⟩, ⟨finishLeft, by decide⟩]

private noncomputable abbrev rightTrace : List grammar.grammar.rules :=
  [⟨splitRight, by decide⟩, ⟨finishRight, by decide⟩]

/-- Two successful derivations of the same word make canceling contributions in one channel. -/
example :
    grammar.contribution 0 [true] leftTrace + grammar.contribution 0 [true] rightTrace = 0 := by
  have hleft : grammar.replay leftTrace = some [.terminal true] := by
    simp [QuantumContextFreeGrammar.replay, ContextFreeRule.rewriteLeftmost]
  have hright : grammar.replay rightTrace = some [.terminal true] := by
    simp [QuantumContextFreeGrammar.replay, ContextFreeRule.rewriteLeftmost]
  have hsplit : splitLeft ≠ splitRight := by decide
  have hfinishLeft : finishLeft ≠ splitRight := by decide
  have hfinishRight : finishRight ≠ splitRight := by decide
  simp [QuantumContextFreeGrammar.contribution, hleft, hright, hsplit, hfinishLeft, hfinishRight]

end CslibFrontierTests.QuantumContextFree
