/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: local-only (ordinary CROSS tail-value transposition clients)

public import CslibFrontier.Computability.PolyTime.CSP.CrossTailTransposition
import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Crossover

/-!
# Ordinary clients for the computed CROSS tail-value transposition

The production Figure 1(b) gadget and its existing ordered witness are used directly.
An accepted unused-port source exercises the complete checker, actual final rows, and
compatible/incompatible directed values. Repeated sparse names, a false closed nullary
row, huge malformed entries, and whole-state short identities exercise the raw contract.
These are single-operation clients, not source hardness or a planarization compiler.
-/

public section

namespace CslibFrontierTests.CSPCrossTailTransposition

open Cslib.Logic.PL Cslib.Logic.PL.CSP Cslib.Logic.PL.CSP.Crossover
open Cslib.Complexity Cslib.Complexity.CSP OrderedBoundary CrossInsertion
open Cslib.BitString Turing.MultiTapeTM

private abbrev g := figureOneB
private abbrev w := figureOneBBoundary

private def unused : State Unit := ⟨[], [10, 20], ⟨[0, 3, 2, 1]⟩⟩

example : unused.Accepted := by decide +kernel

example : (transposeTail g w unused).Accepted :=
  accepted_transposeTail g w unused (by decide +kernel)

-- The checker is applied to the actual emitted table, without replacing it by a witness.
example : OrderedBoundary.verify (transposeTail g w unused).body
    (transposeTail g w unused).ports (transposeTail g w unused).rotation = true :=
  (accepted_transposeTail g w unused (by decide +kernel)).2

example : (transposeTail g w unused).body =
    [⟨(), [40, 20, 9, 7]⟩, ⟨(), [5, 7, 9, 20]⟩] ∧
    (transposeTail g w unused).ports = [5, 7] ∧
    (transposeTail g w unused).rotation.successor.length = 20 := by
  decide +kernel

-- The same semantic witness also fixes an old name absent from both body and ports.
example : ∃ τ : ℕ → Bool, (transposeTail g w unused).body.eval nearSem τ = true ∧
    (∀ z, τ (2 * z) = decide (z = 20)) ∧
    τ (2 * 123456) = false ∧ (transposeTail g w unused).ports.map τ = [true, false] := by
  obtain ⟨τ, ht, he, hv⟩ := (eval_transposeTail_iff g w [] [] 10 20 unused.rotation
    (fun z => decide (z = 20))).mp rfl
  exact ⟨τ, ht, he, by simpa using he 123456, by simpa [unused] using hv⟩

example : ¬∃ τ : ℕ → Bool, (transposeTail g w unused).body.eval nearSem τ = true ∧
    (∀ z, τ (2 * z) = decide (z = 20)) ∧
    (transposeTail g w unused).ports.map τ = [false, true] := by
  rintro ⟨τ, ht, he, hv⟩
  have h := (recover_transposeTail g w [] [] 10 20 unused.rotation τ ht).2
  simp only [List.map_nil, List.nil_append, he] at h
  change (transposeTail g w unused).ports.map τ = _ at h
  rw [hv] at h
  contradiction

private def repeated : State Unit := ⟨[], [2 ^ 250, 17, 17], ⟨[2 ^ 300]⟩⟩

example : (transposeTail g w repeated).ports = [2 * 2 ^ 250, 5, 7] :=
  ports_transposeTail g w [] [2 ^ 250] 17 17 repeated.rotation

example : ∃ τ : ℕ → Bool, (transposeTail g w repeated).body.eval nearSem τ = true ∧
    (∀ z, τ (2 * z) = false) ∧
    (transposeTail g w repeated).ports.map τ = [false, false, false] := by
  simpa only [repeated, List.map_cons, List.map_nil, List.nil_append, List.cons_append]
    using (eval_transposeTail_iff g w [] [2 ^ 250] 17 17 repeated.rotation
    (fun _ => false)).mp rfl

-- Repeated tail values cannot independently change after fusion, even on rejected data.
example : ¬∃ τ : ℕ → Bool, (transposeTail g w repeated).body.eval nearSem τ = true ∧
    (transposeTail g w repeated).ports.map τ = [false, true, false] := by
  rintro ⟨τ, ht, hv⟩
  have h := (recover_transposeTail g w [] [2 ^ 250] 17 17 repeated.rotation τ ht).2
  change (transposeTail g w repeated).ports.map τ = _ at h
  rw [hv] at h
  simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append] at h
  have h1 := (List.cons.inj (List.cons.inj h).2).1
  have h2 := (List.cons.inj (List.cons.inj (List.cons.inj h).2).2).1
  have : (false : Bool) = true := h2.trans h1.symm
  cases this

private def closedFalse : State Unit :=
  ⟨[⟨(), []⟩], [2 ^ 250, 17], ⟨[2 ^ 300, 7]⟩⟩

example : (transposeTail g w closedFalse).body.head? = some ⟨(), []⟩ ∧
    (transposeTail g w closedFalse).body.length = 3 ∧
    (transposeTail g w closedFalse).body.occurrences.length = 8 := by
  decide +kernel

example : ¬∃ τ : ℕ → Bool, (transposeTail g w closedFalse).body.eval nearSem τ = true := by
  rintro ⟨τ, ht⟩
  have h := (recover_transposeTail g w closedFalse.body [] (2 ^ 250) 17
    closedFalse.rotation τ ht).1
  change false = true at h
  contradiction

-- Neither short branch inserts, doubles labels, normalizes a table, or deletes a row.
example : transposeTail g w
    (⟨[⟨(), []⟩], [], ⟨[2 ^ 300, 7, 9]⟩⟩ : State Unit) =
    ⟨[⟨(), []⟩], [], ⟨[2 ^ 300, 7, 9]⟩⟩ := rfl

example : transposeTail g w
    (⟨[⟨(), []⟩], [2 ^ 250], ⟨[2 ^ 300, 7, 9]⟩⟩ : State Unit) =
    ⟨[⟨(), []⟩], [2 ^ 250], ⟨[2 ^ 300, 7, 9]⟩⟩ := rfl

-- The raw runtime certificate has neither an accepted-state premise nor a finite alphabet.
/-- The ordinary client retains the all-raw certificate for arbitrary encoded alphabets. -/
theorem arbitraryRel_runtime {Rel : Type} {ar : Rel → ℕ} {sem : Rel → List Bool → Bool}
    (g : PPGadget ar sem cross) (w : GadgetWitness g) (encRel : Rel ↪ List Bool) :
    ComputableInPolyTime (transposeTail g w) (encState encRel) (encState encRel) :=
  computableInPolyTime_transposeTail g w encRel

example (encRel : Unit ↪ List Bool) (I : State Unit) :
    encState encRel I = encPair (encCSP encRel encNat)
      (encPair (encList encNat) Graph.encRotationCertificate) (I.body, I.ports, I.rotation) := rfl

example (encRel : Unit ↪ List Bool) :
    ComputableInPolyTime (fun I : State Unit => (transposeTail g w I).ports)
      (encState encRel) (encList encNat) :=
  encState_ports_polyTime encRel (computableInPolyTime_transposeTail g w encRel)

end CslibFrontierTests.CSPCrossTailTransposition
