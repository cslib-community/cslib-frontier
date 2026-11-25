/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.ExtendTapes
import CslibFrontier.Foundations.Data.Fin.Embedding

/-!
# Placing work-tape machines onto selected work tapes

Existential wrappers around `TransformsTapes.extendTapes_update`, `Fin.exists_embedding_eq`, and
`Fin.exists_embedding_eq₂` that embed single-tape-preserving and two-tape work-tape machines into
`K` work tapes from cardinality and distinctness bounds without mentioning tidy computability.

## Main results

* `Turing.MultiTapeTM.TransformsTapes.exists_extendTapes_self`: embed a machine preserving work
  tape `i` into `K` work tapes with `i` placed at `V`.
* `Turing.MultiTapeTM.TransformsTapes.exists_extendTapes_pair`: embed a machine reading work tape
  `i` and writing work tape `o` into `K` work tapes with `i` at `V` and `o` at `O`.
-/

namespace Turing.MultiTapeTM

/-- Embed a family of `TransformsTapes` specifications that preserve a single work tape `i` into
`K` work tapes with `i` placed at `V`. -/
public theorem TransformsTapes.exists_extendTapes_self {ι Symbol State : Type*} {k K : ℕ}
    (tm : MultiTapeTM k Symbol State) {inp out : ι → List Symbol} {t s : ι → ℕ}
    {i : Fin k} (hk : k ≤ K) (V : Fin K)
    (h : ∀ a, TransformsTapes tm
      (fun _ ws => True ∧ ws = Function.update (fun _ => []) i (inp a))
      (fun _ ws ws' em => ws' = Function.update ws i (inp a) ∧ em = out a)
      (t a) (s a)) :
    ∃ e : Fin k ↪ Fin K, ∀ a, TransformsTapes (tm.extendTapes e)
      (fun _ ws => ws = Function.update (fun _ => []) V (inp a))
      (fun _ ws ws' em => ws' = ws ∧ em = out a)
      (t a) (s a + (K - k)) := by
  obtain ⟨e, he⟩ := Fin.exists_embedding_eq hk i V
  refine ⟨e, fun a => ?_⟩
  have h' := (h a).extendTapes_update e
  rw [he] at h'
  exact h'.imp (fun _ _ hws => ⟨trivial, hws⟩)
    (fun _ _ _ _ hws ⟨hws', hem⟩ => ⟨by rw [hws', hws, Function.update_idem], hem⟩)
    le_rfl le_rfl

/-- Embed a family of `TransformsTapes` specifications reading distinct work tape `i` and writing
`o` into `K` work tapes with `i` placed at `V` and `o` at `O`. -/
public theorem TransformsTapes.exists_extendTapes_pair {ι Symbol State : Type*} {k K : ℕ}
    (tm : MultiTapeTM k Symbol State) {inp out : ι → List Symbol} {t s : ι → ℕ}
    {i o : Fin k} (hio : i ≠ o) (hk : k ≤ K) {V O : Fin K} (hVO : V ≠ O)
    (h : ∀ a, TransformsTapes tm
      (fun _ ws => ws = Function.update (fun _ => []) i (inp a))
      (fun _ ws ws' em => ws' = Function.update ws o (out a) ∧ em = [])
      (t a) (s a)) :
    ∃ e : Fin k ↪ Fin K, ∀ a, TransformsTapes (tm.extendTapes e)
      (fun _ ws => ws = Function.update (fun _ => []) V (inp a))
      (fun _ ws ws' em => ws' = Function.update ws O (out a) ∧ em = [])
      (t a) (s a + (K - k)) := by
  obtain ⟨e, hi, ho⟩ := Fin.exists_embedding_eq₂ hk hio hVO
  refine ⟨e, fun a => ?_⟩
  have h' := ((h a).imp
    (P' := fun _ ws => True ∧ ws = Function.update (fun _ => []) i (inp a))
    (fun _ _ hws => hws.2) (fun _ _ _ _ _ hq => hq) le_rfl le_rfl).extendTapes_update e
  rw [hi, ho] at h'
  exact h'.imp (fun _ _ hws => ⟨trivial, hws⟩) (fun _ _ _ _ _ hq => hq) le_rfl le_rfl

end Turing.MultiTapeTM
