/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.HWord.RewriteSoundness
import Mathlib.Data.List.OfFn

/-!
# Exact source-rewriting and H-word reachability equivalence

For nonempty source words, every rewrite replays on its canonical encoding, and every legal H-word
trajectory decodes to a real source rewriting trajectory. The finite rule family and target
digraph are fixed independently of word length.

## Main results

* `HWord.RewriteGadget.readout_reachable`: arbitrary intermediate H-words project to source paths.
* `HWord.RewriteGadget.word_reachable_iff`: canonical H-word endpoints are connected exactly when
  their source words are connected by the standard semi-Thue relation.

## References

* [M. Wrochna, *Reconfiguration in bounded bandwidth and treedepth*][Wrochna2014],
  arXiv:1405.0847v1, Section 3, proof of Theorem 3.
-/

public section

namespace Cslib.Complexity.NCL.HWord.RewriteGadget

open Cslib.PostCorrespondence

variable {n q r : ℕ} (rules : Fin r → Rule q)

private theorem rewrite_length {s t : List (Fin q)} (h : Rewrites (RuleSet rules) s t) :
    t.length = s.length := by
  obtain ⟨_, _, _, ⟨_, rfl | rfl⟩, rfl, rfl⟩ := h <;> simp [Rule.domino, Rule.reverse]

/-- Source reachability preserves word length because every rule has two letters on both sides. -/
theorem source_path_length {s t : List (Fin q)}
    (hr : Relation.ReflTransGen (Rewrites (RuleSet rules)) s t) : t.length = s.length := by
  induction hr with
  | refl => rfl
  | tail _ h ih => exact (rewrite_length rules h).trans ih

private theorem word_reachable_of_source_path {s t : Fin n → Fin q}
    (hr : Relation.ReflTransGen (Rewrites (RuleSet rules)) (List.ofFn s) (List.ofFn t)) :
    HWord.Reachable (compatibility rules) (word s) (word t) := by
  suffices ∀ {l}, Relation.ReflTransGen (Rewrites (RuleSet rules)) (List.ofFn s) l →
      ∀ v : Fin n → Fin q, List.ofFn v = l →
        HWord.Reachable (compatibility rules) (word s) (word v) from this hr t rfl
  intro l hpath
  induction hpath with
  | refl => exact fun _ hv => List.ofFn_injective hv ▸ .refl
  | @tail before after hbefore hstep ih =>
    rintro v rfl
    have hlen : before.length = n := by
      simpa only [List.length_ofFn] using source_path_length rules hbefore
    let previous : Fin n → Fin q := fun i => before.get (Fin.cast hlen.symm i)
    have hp : List.ofFn previous = before :=
      (List.ofFn_congr hlen before.get).symm.trans (List.ofFn_get before)
    exact (ih previous hp).trans (word_reachable_of_rewrites rules (hp.symm ▸ hstep))

/-- Every actual H-word trajectory with protected end markers decodes to real source rewriting. -/
theorem readout_reachable
    {u v : Fin (n + 3) → Fin (Fintype.card (Symbol q r))}
    (hr : HWord.Reachable (compatibility rules) u v)
    (hu : HWord.Legal (compatibility rules) u)
    (hstart : u 0 = code .start) (hfinish : u ⟨n + 2, by omega⟩ = code .finish) :
    Relation.ReflTransGen (Rewrites (RuleSet rules)) (List.ofFn (readout rules u hu))
      (List.ofFn (readout rules v (hr.legal hu))) := by
  induction hr with
  | refl => exact .refl
  | tail hbefore hstep ih =>
    obtain ⟨hfirst, hlast⟩ := reachable_boundaries rules hbefore hstart hfinish
    exact ih.trans (step_readout rules hstep hfirst hlast).reflTransGen

/-- Nonempty canonical encodings preserve and reflect standard source reachability. -/
theorem word_reachable_iff (hn : 0 < n) (s t : Fin n → Fin q) :
    HWord.Reachable (compatibility rules) (word s) (word t) ↔
      Relation.ReflTransGen (Rewrites (RuleSet rules)) (List.ofFn s) (List.ofFn t) := by
  constructor
  · intro hr
    have h := readout_reachable rules hr (word_legal rules s hn) (word_start s) (word_finish s)
    simpa only [readout_word rules s hn, readout_word rules t hn] using h
  · exact word_reachable_of_source_path rules

end Cslib.Complexity.NCL.HWord.RewriteGadget
