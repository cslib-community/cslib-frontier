/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module

public import CslibFrontier.Computability.PolyTime.CSP.CrossTranspositionSchedule
import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Crossover
import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.AtomBoundary

/-!
# Ordinary clients of the actual CROSS schedule fold

Production Figure1(b) and its witness are reused once. A production atom certificate
checks two noncommuting schedules. Equal value words after a repeated request do not
imply raw-State involution. Huge invalid indices, false/nullary rows, repeated sparse
names and unrestricted encoded alphabets exercise the all-raw and recovery contracts.
-/

public section

namespace CslibFrontierTests.CSPCrossTranspositionSchedule

open Cslib.Logic.PL Cslib.Logic.PL.CSP Cslib.Logic.PL.CSP.Crossover
open Cslib.Complexity Cslib.Complexity.CSP OrderedBoundary CrossInsertion
open Cslib.BitString Turing.MultiTapeTM

private abbrev g := figureOneB
private abbrev w := figureOneBBoundary

-- A literal original relation row with the existing production arbitrary-arity atom table.
private def atom : State Unit :=
  ⟨[⟨(), [10,20,30,40]⟩], [10,20,30,40], atomBoundaryCertificate 4⟩

private def sigma (z : ℕ) : Bool := decide (z=20 ∨ z=40)

example : atom.Accepted := by decide +kernel

example : (transposeSchedule g w atom [0,1]).Accepted ∧
    (transposeSchedule g w atom [1,0]).Accepted :=
  ⟨accepted_transposeSchedule g w atom _ (by decide +kernel),
    accepted_transposeSchedule g w atom _ (by decide +kernel)⟩

example : OrderedBoundary.verify (transposeSchedule g w atom [0,1]).body
    (transposeSchedule g w atom [0,1]).ports (transposeSchedule g w atom [0,1]).rotation = true :=
  (accepted_transposeSchedule g w atom _ (by decide +kernel)).2

example : ∃ τ : ℕ → Bool, (transposeSchedule g w atom [0,1]).body.eval nearSem τ = true ∧
    (∀ z, τ (4*z)=sigma z) ∧ τ (4*123456)=false ∧
    (transposeSchedule g w atom [0,1]).ports.map τ = [true,false,false,true] := by
  obtain ⟨τ, ht, he, hv⟩ := (eval_transposeSchedule_iff g w atom [0,1] sigma).mp (by decide +kernel)
  change ∀ z, τ (4*z)=sigma z at he
  change _ = [sigma 20,sigma 30,sigma 10,sigma 40] at hv
  exact ⟨τ,ht,he,by simpa [sigma] using he 123456,by simpa [sigma] using hv⟩

example : ∃ τ : ℕ → Bool, (transposeSchedule g w atom [1,0]).body.eval nearSem τ = true ∧
    (∀ z, τ (4*z)=sigma z) ∧
    (transposeSchedule g w atom [1,0]).ports.map τ = [false,false,true,true] := by
  obtain ⟨τ,ht,he,hv⟩ := (eval_transposeSchedule_iff g w atom [1,0] sigma).mp (by decide +kernel)
  change ∀ z, τ (4*z)=sigma z at he
  change _ = [sigma 30,sigma 10,sigma 20,sigma 40] at hv
  exact ⟨τ,ht,he,by simpa [sigma] using hv⟩

-- ONE final assignment recovers source satisfaction and the whole word, not just existence.
example (τ : ℕ → Bool) (ht : (transposeSchedule g w atom [0, 1]).body.eval nearSem τ = true) :
    atom.body.eval nearSem (fun z => τ (4*z)) = true ∧
      (transposeSchedule g w atom [0,1]).ports.map τ =
        [τ (4*20),τ (4*30),τ (4*10),τ (4*40)] := by
  exact recover_transposeSchedule g w atom [0,1] τ ht

example : ¬∃ τ : ℕ → Bool, (transposeSchedule g w atom [0,1]).body.eval nearSem τ = true ∧
    (∀ z, τ (4*z)=sigma z) ∧
    (transposeSchedule g w atom [0,1]).ports.map τ = [false,false,true,true] := by
  rintro ⟨τ,ht,he,hv⟩
  have h := (recover_transposeSchedule g w atom [0,1] τ ht).2
  change _ = [τ (4*20),τ (4*30),τ (4*10),τ (4*40)] at h
  simp only [he] at h
  rw [hv] at h
  simp [sigma] at h

example : ∃ τ : ℕ → Bool, (transposeSchedule g w atom [0,0]).body.eval nearSem τ = true ∧
    (∀ z, τ (4*z)=sigma z) ∧
    (transposeSchedule g w atom [0,0]).ports.map τ = atom.ports.map sigma := by
  exact (eval_transposeSchedule_iff g w atom [0,0] sigma).mp (by decide +kernel)

example : (transposeSchedule g w atom [0,0]).body.length = 5 ∧
    (transposeSchedule g w atom [0,0]).body.occurrences.length = 20 ∧
    (transposeSchedule g w atom [0,0]).ports.length = 4 := by
  have h := components_transposeSchedule g w atom [0,0]
  simpa [atom, g, figureOneB, figureOneBBody, CSP.length_occurrences] using
    ⟨h.1,h.2.1,h.2.2.1⟩

example : transposeSchedule g w atom [0,0] ≠ atom := by
  intro h
  have hq := congrArg (fun I : State Unit => I.body.length) h
  have h := (components_transposeSchedule g w atom [0,0]).1
  simp [atom, g, figureOneB, figureOneBBody] at hq h
  omega

private def broken : State Unit :=
  ⟨[⟨(),[]⟩,⟨(),[17,17]⟩,⟨(),[17,17]⟩], [2^250,17,17,2^250], ⟨[2^300,9,9]⟩⟩

example : transposeSchedule g w broken [] = broken := rfl

example : transposeSchedule g w broken [2^300,3,2^300] = broken :=
  transposeSchedule_eq_self g w broken _ (by
    intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with hj | hj | hj
    all_goals rw [hj]; decide +kernel)


-- Invalid calls are exact identity, so only the single valid request contributes a doubling.
example : transposeSchedule g w broken [2^300,0,2^300] = transposeAdjacent g w broken 0 := by
  simp only [transposeSchedule, List.foldl_cons, List.foldl_nil]
  rw [transposeAdjacent_invalid g w broken _ (by decide +kernel)]
  apply transposeAdjacent_invalid
  have h := (counts_transposeAdjacent g w broken 0).2.2
  rw [h]
  decide +kernel

example : ∃ τ : ℕ → Bool,
    (transposeSchedule g w atom [2^300,0,2^300]).body.eval nearSem τ = true ∧
    (∀ z, τ (2*z)=sigma z) ∧
    (transposeSchedule g w atom [2^300,0,2^300]).ports.map τ = [true,false,false,true] := by
  obtain ⟨τ,ht,he,hv⟩ := (eval_transposeSchedule_iff g w atom [2^300,0,2^300] sigma).mp
    (by decide +kernel)
  have hk : ([2^300, 0, 2^300] : List ℕ).countP
      (fun j => decide (j+1<atom.ports.length)) = 1 := by decide +kernel
  simp only [hk, pow_one] at he
  exact ⟨τ, ht, he, hv.trans (by decide +kernel)⟩

example : (transposeSchedule g w broken [2^300,0,2^300]).body.length = 5 := by
  have h := (components_transposeSchedule g w broken [2^300,0,2^300]).1
  have hk : ([2^300, 0, 2^300] : List ℕ).countP
      (fun j => decide (j+1<4)) = 1 := by decide +kernel
  rw [show broken.ports.length = 4 from rfl, hk] at h
  exact h

-- Both duplicate indexed rows and the false closed nullary row remain in the old prefix.
example : ((transposeSchedule g w broken [0]).body.take 3).map (fun c => c.scope.length) =
    [0,2,2] := by decide +kernel

example : ¬∃ τ : ℕ → Bool, (transposeSchedule g w broken [0,1]).body.eval nearSem τ = true := by
  rintro ⟨τ,ht⟩
  have h := (recover_transposeSchedule g w broken [0,1] τ ht).1
  change false = true at h
  cases h

example : ¬(transposeSchedule g w broken [0,1]).body.WellFormed (fun _ => 4) := by
  rw [wellFormed_transposeSchedule_iff]
  decide +kernel

example {Rel : Type} {ar : Rel → ℕ} {sem : Rel → List Bool → Bool}
    (g : PPGadget ar sem cross) (w : GadgetWitness g) (I : State Rel) (js : List ℕ)
    (h : ¬I.body.WellFormed ar) : ¬(transposeSchedule g w I js).body.WellFormed ar :=
  fun hout => h ((wellFormed_transposeSchedule_iff g w I js).mp hout)

private def repeated : State Unit := ⟨[],[2^250,17,17,2^250],⟨[2^300]⟩⟩

example : ∃ τ : ℕ → Bool, (transposeSchedule g w repeated [1,0]).body.eval nearSem τ = true ∧
    (∀ z, τ (4*z)=false) ∧
    (transposeSchedule g w repeated [1,0]).ports.map τ = [false,false,false,false] := by
  exact (eval_transposeSchedule_iff g w repeated [1,0] (fun _ => false)).mp rfl

example : ¬∃ τ : ℕ → Bool, (transposeSchedule g w repeated [1,0]).body.eval nearSem τ = true ∧
    (transposeSchedule g w repeated [1,0]).ports.map τ = [true,false,false,false] := by
  rintro ⟨τ,ht,hv⟩
  have h := (recover_transposeSchedule g w repeated [1,0] τ ht).2
  change _ = [τ (4*17),τ (4*2^250),τ (4*17),τ (4*2^250)] at h
  rw [hv] at h
  cases hb : τ (4*17) <;> simp only [hb, List.cons.injEq] at h <;> tauto

example (c : Graph.RotationCertificate) (js : List ℕ) :
    transposeSchedule g w (⟨broken.body,[],c⟩ : State Unit) js = ⟨broken.body,[],c⟩ :=
  transposeSchedule_eq_self g w _ _ (by intro j _; simp)

example (c : Graph.RotationCertificate) (js : List ℕ) :
    transposeSchedule g w (⟨broken.body,[2^250],c⟩ : State Unit) js =
      ⟨broken.body,[2^250],c⟩ :=
  transposeSchedule_eq_self g w _ _ (by intro j _; change 1 ≤ j+1; omega)

/-- The schedule runtime certificate admits arbitrary encoded relation alphabets. -/
theorem computableInPolyTime_anyRel {Rel : Type} {ar : Rel → ℕ} {sem : Rel → List Bool → Bool}
    (g : PPGadget ar sem cross) (w : GadgetWitness g) (encRel : Rel ↪ List Bool) :
    ComputableInPolyTime (fun p : State Rel × List ℕ => transposeSchedule g w p.1 p.2)
      (encPair (encState encRel) (encList encNat)) (encState encRel) :=
  computableInPolyTime_transposeSchedule g w encRel

example (encRel : Unit ↪ List Bool) :
    ComputableInPolyTime (fun p : State Unit × List ℕ => (transposeSchedule g w p.1 p.2).ports)
      (encPair (encState encRel) (encList encNat)) (encList encNat) :=
  encState_ports_polyTime encRel (computableInPolyTime_transposeSchedule g w encRel)

end CslibFrontierTests.CSPCrossTranspositionSchedule
