/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.KernelOnWords
import CslibFrontier.Foundations.Data.Fin.Embedding

/-!
# Placing tidy machines onto selected work tapes

Existential wrappers around `ComputesTidilyInTimeAndSpace.inputFromWord_extendTapes` and
`ComputesTidilyInTimeAndSpace.onWords_extendTapes` that construct the tape-selection embedding
into `K` work tapes from cardinality and distinctness bounds.

## Main results

* `Turing.MultiTapeTM.exists_inputFromWord_extendTapes`: embed `tm.inputFromWord mark` into `K`
  work tapes with its input tape placed at `V`.
* `Turing.MultiTapeTM.exists_onWords_extendTapes`: embed `tm.onWords mark` into `K` work tapes
  with its input tape at `V` and output tape at `O`.
-/

namespace Turing.MultiTapeTM

/-- Embed `tm.inputFromWord mark` into `K` work tapes with its input tape placed at `V`. -/
public theorem exists_inputFromWord_extendTapes {ι Symbol State : Type*} {k K : ℕ}
    (mark : Symbol) (tm : MultiTapeTM k Symbol State) {inp out : ι → List Symbol}
    {t s : ι → ℕ} (htm : ∀ a, tm.ComputesTidilyInTimeAndSpace (inp a) (out a) (t a) (s a))
    (hk : k + 2 ≤ K) (V : Fin K) :
    ∃ e : Fin (k + 2) ↪ Fin K, ∀ a, TransformsTapes ((tm.inputFromWord mark).extendTapes e)
      (fun _ ws => ws = Function.update (fun _ => []) V (inp a))
      (fun _ ws ws' em => ws' = ws ∧ em = out a)
      (t a + 4) (s a + 2 * ((inp a).length + 2) + 2 * k + 8 + (K - (k + 2))) := by
  obtain ⟨e, he⟩ := Fin.exists_embedding_eq hk (Fin.natAdd k (0 : Fin 2)) V
  exact ⟨e, fun a => (htm a).inputFromWord_extendTapes mark he⟩

/-- Embed `tm.onWords mark` into `K` work tapes with its input tape at `V` and output tape at
`O`. -/
public theorem exists_onWords_extendTapes {ι Symbol State : Type*} {k K : ℕ}
    (mark : Symbol) (tm : MultiTapeTM k Symbol State) {inp out : ι → List Symbol}
    {t s : ι → ℕ} (htm : ∀ a, tm.ComputesTidilyInTimeAndSpace (inp a) (out a) (t a) (s a))
    (hk : k + 1 + 2 ≤ K) {V O : Fin K} (hVO : V ≠ O) :
    ∃ e : Fin (k + 1 + 2) ↪ Fin K, ∀ a, TransformsTapes ((tm.onWords mark).extendTapes e)
      (fun _ ws => ws = Function.update (fun _ => []) V (inp a))
      (fun _ ws ws' em => ws' = Function.update ws O (out a) ∧ em = [])
      (t a + (out a).length + 6)
      (s a + 2 * (inp a).length + 2 * (out a).length + 3 * k + 18 + (K - (k + 1 + 2))) := by
  obtain ⟨e, hi, ho⟩ := Fin.exists_embedding_eq₂ hk (i := Fin.natAdd (k + 1) (0 : Fin 2))
    (o := (Fin.last k).castAdd 2) (by simp [Fin.ext_iff]) hVO
  exact ⟨e, fun a => (htm a).onWords_extendTapes mark hi ho⟩

end Turing.MultiTapeTM
