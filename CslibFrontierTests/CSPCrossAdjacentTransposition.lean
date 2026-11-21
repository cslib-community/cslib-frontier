/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module

public import CslibFrontier.Computability.PolyTime.CSP.CrossAdjacentTransposition
import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Crossover

/-!
# Positioned CROSS routing through ordinary imports

The production Figure 1(b) gadget/witness is used once. Positive and negative directed
values, actual emitted tables, repeated sparse names, false/nullary rows, malformed scopes,
invalid huge binary positions and whole-state short identity exercise the raw contract.
These clients assert no compiler, schedule bound or original-language hardness theorem.
-/

public section

namespace CslibFrontierTests.CSPCrossAdjacentTransposition

open Cslib.Logic.PL Cslib.Logic.PL.CSP Cslib.Logic.PL.CSP.Crossover
open Cslib.Complexity Cslib.Complexity.CSP OrderedBoundary CrossInsertion
open Cslib.BitString Turing.MultiTapeTM

private abbrev g := figureOneB
private abbrev w := figureOneBBoundary

private def unused : State Unit := ⟨[], [10, 20, 30, 40], ⟨[0, 3, 2, 5, 4, 7, 6, 1]⟩⟩

/-- The literal production boundary fixture passes both full input checks. -/
theorem four_port_source_accepted :
    (⟨[], [10, 20, 30, 40], ⟨[0, 3, 2, 5, 4, 7, 6, 1]⟩⟩ : State Unit).Accepted := by
  decide +kernel

example : (transposeAdjacent g w unused 1).Accepted :=
  accepted_transposeAdjacent g w unused 1 (by decide +kernel)

example : OrderedBoundary.verify (transposeAdjacent g w unused 1).body
    (transposeAdjacent g w unused 1).ports (transposeAdjacent g w unused 1).rotation = true :=
  (accepted_transposeAdjacent g w unused 1 (by decide +kernel)).2

example : (transposeAdjacent g w unused 1).ports = [20, 5, 7, 80] ∧
    (transposeAdjacent g w unused 1).body =
      [⟨(), [60, 40, 9, 7]⟩, ⟨(), [5, 7, 9, 40]⟩] ∧
    (transposeAdjacent g w unused 1).rotation.successor.length = 24 := by
  decide +kernel

-- Numeric projections are of the literal executed program, not a replacement certificate.
example : (transposeAdjacent g w unused 1).rotation =
    (rotateLeft (transposeTail g w (rotateRight unused))).rotation := rfl

example : (transposeAdjacent g w unused 0).ports = [5, 7, 60, 80] :=
  ports_transposeAdjacent g w [] [] 10 20 [30, 40] unused.rotation

example : transposeAdjacent g w unused 2 = transposeTail g w unused :=
  transposeAdjacent_tail g w [] [10, 20] 30 40 unused.rotation

private def sigma (z : ℕ) : Bool := decide (z = 30 ∨ z = 40)

example : ∃ τ : ℕ → Bool, (transposeAdjacent g w unused 1).body.eval nearSem τ = true ∧
    (∀ z, τ (2 * z) = sigma z) ∧ τ (2 * 123456) = false ∧
    (transposeAdjacent g w unused 1).ports.map τ = [false, true, false, true] := by
  obtain ⟨τ, ht, he, hv⟩ :=
    (eval_transposeAdjacent_iff g w [] [10] 20 30 [40] unused.rotation sigma).mp rfl
  exact ⟨τ, ht, he, by simpa [sigma] using he 123456, by simpa [sigma, unused] using hv⟩

example : ¬∃ τ : ℕ → Bool, (transposeAdjacent g w unused 1).body.eval nearSem τ = true ∧
    (∀ z, τ (2 * z) = sigma z) ∧
    (transposeAdjacent g w unused 1).ports.map τ = [false, false, true, true] := by
  rintro ⟨τ, ht, he, hv⟩
  have h := (recover_transposeAdjacent g w [] [10] 20 30 [40] unused.rotation τ ht).2
  simp only [he] at h
  change (transposeAdjacent g w unused 1).ports.map τ = _ at h
  rw [hv] at h
  simp [sigma] at h

private def repeated : State Unit :=
  ⟨[], [2 ^ 250, 17, 17, 2 ^ 250], ⟨[2 ^ 300]⟩⟩

example : (transposeAdjacent g w repeated 1).ports = [2 * 2 ^ 250, 5, 7, 2 * 2 ^ 250] :=
  ports_transposeAdjacent g w [] [2 ^ 250] 17 17 [2 ^ 250] repeated.rotation

example : ∃ τ : ℕ → Bool, (transposeAdjacent g w repeated 1).body.eval nearSem τ = true ∧
    (∀ z, τ (2 * z) = false) ∧
    (transposeAdjacent g w repeated 1).ports.map τ = [false, false, false, false] := by
  simpa only [repeated, List.length_cons, List.length_nil,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append] using
    (eval_transposeAdjacent_iff g w [] [2 ^ 250] 17 17 [2 ^ 250] repeated.rotation
      (fun _ => false)).mp rfl

private def malformed : State Unit :=
  ⟨[⟨(), []⟩, ⟨(), [17, 17]⟩], [2 ^ 250, 17, 17], ⟨[2 ^ 300, 9]⟩⟩

example : transposeAdjacent g w malformed (2 ^ 300) = malformed :=
  transposeAdjacent_invalid g w malformed _ (by decide +kernel)

example : transposeAdjacent g w malformed 2 = malformed :=
  transposeAdjacent_invalid g w malformed _ (by decide +kernel)

example : (transposeAdjacent g w malformed 0).body.head? = some ⟨(), []⟩ ∧
    (transposeAdjacent g w malformed 0).body.length = 4 := by
  decide +kernel

-- Arity rejection is independent of what arbitrary semantics might assign wrong lengths.
example {Rel : Type} {ar : Rel → ℕ} {sem : Rel → List Bool → Bool}
    (g : PPGadget ar sem cross) (w : GadgetWitness g) (I : State Rel) (j : ℕ)
    (h : ¬I.body.WellFormed ar) : ¬(transposeAdjacent g w I j).body.WellFormed ar :=
  fun ho => h ((wellFormed_transposeAdjacent_iff g w I j).mp ho)

example : ¬(transposeAdjacent g w malformed 0).body.WellFormed (fun _ => 4) := by
  rw [wellFormed_transposeAdjacent_iff]
  decide +kernel

example : (transposeAdjacent g w unused 1).rotation.successor =
    [0, 3, 14, 5, 12, 7, 10, 1, 20, 11, 18, 13,
      4, 15, 2, 9, 16, 19, 6, 21, 8, 23, 22, 17] := by
  unfold transposeAdjacent unused transposeTail rotateLeft rotateRight fuseHead hideHead
    CrossInsertion.insert g w
  rw [figureOneBBoundary_certificate]
  decide +kernel

example : ¬∃ τ : ℕ → Bool, (transposeAdjacent g w malformed 0).body.eval nearSem τ = true := by
  rintro ⟨τ, ht⟩
  have h := (recover_transposeAdjacent g w malformed.body [] (2 ^ 250) 17 [17]
    malformed.rotation τ ht).1
  change false = true at h
  cases h

example (c : Graph.RotationCertificate) :
    transposeAdjacent g w (⟨malformed.body, [], c⟩ : State Unit) 0 =
      ⟨malformed.body, [], c⟩ :=
  transposeAdjacent_invalid g w _ _ (by change (0 : ℕ) ≤ 1; omega)

example (c : Graph.RotationCertificate) :
    transposeAdjacent g w (⟨malformed.body, [2 ^ 250], c⟩ : State Unit) 0 =
      ⟨malformed.body, [2 ^ 250], c⟩ :=
  transposeAdjacent_invalid g w _ _ (by change (1 : ℕ) ≤ 1; omega)

-- A positive raw full cycle need not be identity: never reduce the executed loop count mod P.
example : (rotateLeft (rotateLeft (⟨[], [10, 20], ⟨[]⟩⟩ : State Unit))).rotation.successor =
    [0, 0, 0, 0] ∧
    rotateLeft (rotateLeft (⟨[], [10, 20], ⟨[]⟩⟩ : State Unit)) ≠ ⟨[], [10, 20], ⟨[]⟩⟩ := by
  have htable : (rotateLeft (rotateLeft (⟨[], [10, 20], ⟨[]⟩⟩ : State Unit))).rotation.successor =
      [0, 0, 0, 0] := by decide +kernel
  refine ⟨htable, ?_⟩
  intro h
  have hnil := congrArg (fun I : State Unit => I.rotation.successor) h
  rw [htable] at hnil
  cases hnil

example {Rel : Type} {ar : Rel → ℕ} {sem : Rel → List Bool → Bool}
    (g : PPGadget ar sem cross) (w : GadgetWitness g) (encRel : Rel ↪ List Bool) :
    ComputableInPolyTime (fun p : State Rel × ℕ => transposeAdjacent g w p.1 p.2)
      (encPair (encState encRel) encNat) (encState encRel) :=
  computableInPolyTime_transposeAdjacent g w encRel

example (encRel : Unit ↪ List Bool) :
    ComputableInPolyTime
      (fun p : State Unit × ℕ => (transposeAdjacent g w p.1 p.2).ports)
      (encPair (encState encRel) encNat) (encList encNat) :=
  encState_ports_polyTime encRel (computableInPolyTime_transposeAdjacent g w encRel)

example (encRel : Unit ↪ List Bool) (I : State Unit) :
    encState encRel I = encPair (encCSP encRel encNat)
      (encPair (encList encNat) Graph.encRotationCertificate) (I.body, I.ports, I.rotation) := rfl

end CslibFrontierTests.CSPCrossAdjacentTransposition
