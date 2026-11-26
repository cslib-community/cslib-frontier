/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Space
public import CslibFrontier.Computability.Complexity.Problems.NCL.HWord.RewriteReduction
import CslibFrontier.Computability.Complexity.Classes.Space.TQBF.Prenex
import CslibFrontier.Computability.Complexity.Problems.NCL.HWord.RewriteTable
import CslibFrontier.Computability.Complexity.Problems.NCL.HWord.TM0Encoding
import CslibFrontier.Computability.Machines.Turing.TM2.WindowSpace

/-!
# PSPACE-hardness for fixed rewriting and fixed H-word reconfiguration

A polynomial-space decider for alternating prenex CNF truth supplies one fixed finite tape
machine. Its polynomially padded input and true-halt windows are produced in polynomial time.
The machine's finite local rules are numbered once and used for every input length.
The reductions use the standard framed two-word encodings and ordinary polynomial-time
many-one reducibility.

## Main results

* `HWord.exists_sourceLanguage_pspaceHard`: one fixed symmetric two-letter rule table is hard.
* `HWord.exists_language_pspaceHard`: one fixed finite directed graph has hard word reconfiguration.

## References

* [M. Wrochna, *Reconfiguration in bounded bandwidth and treedepth*][Wrochna2014],
  arXiv:1405.0847v1, Sections 2–3, hardness directions of Theorems 1 and 3.
-/

public section

namespace Cslib.Complexity.NCL.HWord

open _root_.Turing _root_.Turing.MultiTapeTM RewriteGadget

private theorem exists_sourceReduction {α : Type} {encIn : α ↪ List Bool} {A : Set α}
    (hA : A ∈ PSPACE encIn) :
    ∃ (q r : ℕ) (rules : Fin r → Rule q),
      PolyTimeReducible encIn (encInstance q) A (sourceLanguage rules) := by
  obtain ⟨f, h, hfinite, p, hpath⟩ := mem_PSPACE_exists_windowTM0 hA
  let : ∀ k, Finite (h.tm.Γ k) := hfinite
  let Γ := TM2to1.Γ' h.tm.K h.tm.Γ
  let Q := FinTM2.TM0Control h.tm
  let : Fintype Γ := Fintype.ofFinite Γ
  let : Fintype (TM0Window.Symbol Γ Q) := Fintype.ofFinite _
  let M := h.tm.toTM0
  let T := RuleTable.ofFinite (TM0Window.Rules.Rule M) (TM0Window.Rules.finite_rule M)
    (fun _ hd => TM0Window.Rules.rule_shape hd)
  refine ⟨Fintype.card (TM0Window.Symbol Γ Q), T.size, T.entries, ?_⟩
  refine ⟨(fun a => {
    source := TM0Window.numberedWord (h.inputWindow p a)
    target := TM0Window.numberedWord (h.haltWindow p a true) }), ?_, ?_⟩
  · exact encInstance_mk_polyTime _
      (TM0Window.computableInPolyTime_numberedWord.comp (h.computableInPolyTime_inputWindow p))
      (TM0Window.computableInPolyTime_numberedWord.comp
        (h.computableInPolyTime_haltWindow p true))
  · intro a
    change a ∈ A ↔ Relation.ReflTransGen (Cslib.PostCorrespondence.Rewrites (RuleSet T.entries))
      ((TM0Window.Rules.word (.stable (h.inputWindow p a))).map
        (Fintype.equivFin (TM0Window.Symbol Γ Q)))
      ((TM0Window.Rules.word (.stable (h.haltWindow p a true))).map
        (Fintype.equivFin (TM0Window.Symbol Γ Q)))
    exact (hpath a).trans
      ((TM0Window.Rules.symmetric_reaches_halted_iff M _ _
        (h.haltWindow_terminal p a true)).symm.trans
        (T.reachable_iff _ _))

/-- One fixed finite symmetric family of two-letter, single-letter-change rewriting rules is
PSPACE-hard under the standard two-word encoding. -/
theorem exists_sourceLanguage_pspaceHard :
    ∃ (q r : ℕ) (rules : Fin r → Rule q), PSPACEHard (encInstance q) (sourceLanguage rules) := by
  obtain ⟨q, r, rules, hreduce⟩ := exists_sourceReduction TQBFCNF_mem_PSPACE
  exact ⟨q, r, rules, TQBFCNF_pspaceHard.trans hreduce⟩

/-- One fixed finite directed graph with a nonempty alphabet has PSPACE-hard word reconfiguration
under the standard two-word encoding. The word length remains part of the input. -/
theorem exists_language_pspaceHard :
    ∃ (q : ℕ) (H : Digraph (Fin q)), 0 < q ∧ PSPACEHard (encInstance q) (language H) := by
  obtain ⟨q, r, rules, hhard⟩ := exists_sourceLanguage_pspaceHard
  exact ⟨_, compatibility rules, Fintype.card_pos_iff.mpr ⟨(.start : Symbol q r)⟩,
    hhard.trans (polyTimeReducible_sourceLanguage rules)⟩

end Cslib.Complexity.NCL.HWord
