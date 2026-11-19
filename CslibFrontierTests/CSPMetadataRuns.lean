/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module

public import CslibFrontier.Computability.PolyTime.CSP.SortMetadataRuns
import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.AtomBoundary
import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Crossover
import Mathlib.Tactic.IntervalCases

/-!
# Ordinary clients of the computed all-metadata-runs driver

Production atom certificates and Figure 1(b) exercise one sort followed by multiple actual
closures. Global cross-group name collisions, direct one-output recovery, unchanged-name
forwarding, empty/mismatch identities and malformed data are tested separately. Equality is
not inferred from arbitrary output values at eliminated names.
-/

public section

namespace CslibFrontierTests.CSPMetadataRuns

open Cslib.Logic.PL Cslib.Logic.PL.CSP Cslib.Logic.PL.CSP.Crossover
open Cslib.Complexity Cslib.Complexity.CSP OrderedBoundary CrossInsertion
open Cslib.AdjacentSortTrace Turing.MultiTapeTM Cslib.BitString

private abbrev g := figureOneB
private abbrev w := figureOneBBoundary
private def atom : State Unit :=
  ⟨[⟨(),[10,20,30,40]⟩],[10,20,30,40],atomBoundaryCertificate 4⟩
private def keys : List ℕ := [2,1,2,1]
private def sigma (z : ℕ) : Bool := decide (z=20 ∨ z=40)

private theorem computed_keys : compute keys = ⟨[1,1,2,2],[2,0,1]⟩ := by
  simp [keys,compute,Cslib.AdjacentSortTrace.insert,List.range_succ]

example : compute keys = ⟨[1,1,2,2],[2,0,1]⟩ ∧
    (sortBoundaryMetadata g w atom keys).ports = [10,5,7,28] := by
  refine ⟨computed_keys,?_⟩
  rw [sortBoundaryMetadata,computed_keys]
  decide +kernel

example : sortAndCloseMetadataRuns g w atom keys = hideHead (fuseHead (hideHead (fuseHead
  (sortBoundaryMetadata g w atom keys)))) := by
  rw [sortAndCloseMetadataRuns,sortBoundaryMetadata,computed_keys]
  rfl

example : (sortAndCloseMetadataRuns g w atom keys).ports = [] ∧
    (sortAndCloseMetadataRuns g w atom keys).body.length = 7 ∧
    (sortAndCloseMetadataRuns g w atom keys).body.occurrences.length = 28 ∧
    (sortAndCloseMetadataRuns g w atom keys).rotation.successor.length = 56 := by
  rw [sortAndCloseMetadataRuns,computed_keys,closeMetadataRuns]
  decide +kernel

example : (sortAndCloseMetadataRuns g w atom keys).Accepted :=
  accepted_sortAndCloseMetadataRuns g w atom keys (by decide +kernel)

example : verifyRotationCertificate (sortAndCloseMetadataRuns g w atom keys).body
    (sortAndCloseMetadataRuns g w atom keys).rotation = true :=
  body_accepted_sortAndCloseMetadataRuns g w atom keys rfl (by decide +kernel)

example : (sortAndCloseMetadataRuns g w atom keys).body.map
      (fun c => (c.rel,c.scope.length)) = (sortBoundaryMetadata g w atom keys).body.map (fun c =>
        (c.rel,c.scope.length)) :=
  (components_sortAndCloseMetadataRuns g w atom keys rfl).2.2.2.1

example : ∃ τ : ℕ → Bool,
    (sortAndCloseMetadataRuns g w atom keys).body.eval nearSem τ = true ∧
      (∀ z,τ (8*z) = sigma z) ∧ τ (8*123456) = false := by
  obtain ⟨τ,ht,ha⟩ := forward_sortAndCloseMetadataRuns g w atom keys rfl sigma
    (by decide +kernel) (by
      intro i j hi hj he
      change i<4 at hi
      change j<4 at hj
      interval_cases i <;> interval_cases j <;> simp_all [keys,atom,sigma])
  have hc : (compute keys).requests.length=3 := by rw [computed_keys]; rfl
  rw [hc] at ha
  change ∀ z,τ (8*z)=sigma z at ha
  exact ⟨τ,ht,ha,by simpa [sigma] using ha 123456⟩

-- This client names only the explicitly specified public finite-prefix map, not a private
-- source proof helper. It is derived from the actual sorted State and actual run callbacks.
private def recovered (τ : ℕ → Bool) (z : ℕ) : Bool :=
  let sorted := (compute keys).sortedKeys
  let J := sortBoundaryMetadata g w atom keys
  let states := fun s => (fun K : State Unit => closeFirstMetadataRun K
    (sorted.drop (sorted.length-K.ports.length)))^[s] J
  let Phi := (List.range sorted.length).foldl (fun f s => fun x =>
    if f x ∈ (states s).ports.take
        ((sorted.drop (sorted.length-(states s).ports.length)).takeWhile
          (fun b => decide (b=(sorted.drop (sorted.length-(states s).ports.length)).headD
            0))).length
    then (states s).ports.headD 0 else f x) id
  τ (Phi (2^(compute keys).requests.length*z))

private theorem source_recovery (τ : ℕ → Bool)
    (ht : (sortAndCloseMetadataRuns g w atom keys).body.eval nearSem τ = true) :
    atom.body.eval nearSem (recovered τ) = true ∧
      recovered τ 10 = recovered τ 30 ∧ recovered τ 20 = recovered τ 40 := by
  have h := recover_sortAndCloseMetadataRuns g w atom keys rfl τ ht
  change atom.body.eval nearSem (recovered τ)=true ∧ _ at h
  have h02 := h.2.2 0 2 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have h13 := h.2.2 1 3 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact ⟨h.1,h02,h13⟩

example (τ : ℕ → Bool)
    (ht : (sortAndCloseMetadataRuns g w atom keys).body.eval nearSem τ = true) :
    atom.body.eval nearSem (recovered τ) = true ∧
      recovered τ 10 = recovered τ 30 ∧ recovered τ 20 = recovered τ 40 := source_recovery τ ht

example : ¬∃ τ : ℕ → Bool,
    (sortAndCloseMetadataRuns g w atom keys).body.eval nearSem τ = true ∧
      recovered τ 20 ≠ recovered τ 40 := by
  rintro ⟨τ,ht,hne⟩
  exact hne (source_recovery τ ht).2.2

private def raw (ports : List ℕ) (table : List ℕ := []) : State Unit := ⟨[],ports,⟨table⟩⟩

-- Three singleton groups execute three hides, and no fusion.
example : closeMetadataRuns (raw [9,4,2]) [1,2,1] = hideHead (hideHead (hideHead (raw [9,4,2])))
  := by rfl

-- One three-member run executes two fusions and one hide. Padded callbacks are identities.
example : closeMetadataRuns (raw [9,4,2]) [1,1,1] = hideHead (fuseHead (fuseHead (raw [9,4,2])))
  := by rfl

example : let J := raw [9,4,2]
    let next := fun K : State Unit => closeFirstMetadataRun K ([1,1,1].drop (3-K.ports.length))
    next (next J) = next J ∧ next (next (next J)) = next J := by exact ⟨rfl,rfl⟩

example : let J := sortBoundaryMetadata g w atom keys
    let next := fun K : State Unit => closeFirstMetadataRun K ([1,1,2,2].drop (4-K.ports.length))
    next (next (next J)) = next (next J) ∧
      next (next (next (next J))) = next (next J) := by
  dsimp only
  let J := sortBoundaryMetadata g w atom keys
  let next := fun K : State Unit => closeFirstMetadataRun K ([1,1,2,2].drop (4-K.ports.length))
  change next (next (next J))=next (next J) ∧
    next (next (next (next J)))=next (next J)
  have hz : (next (next J)).ports=[] := by
    dsimp only [next,J]
    rw [sortBoundaryMetadata,computed_keys]
    decide +kernel
  have hfix : next (next (next J))=next (next J) := by
    apply closeFirstMetadataRun_eq_self
    right
    rw [hz]
    rfl
  exact ⟨hfix,(congrArg next hfix).trans hfix⟩

-- Low unsorted metadata closes three runs; the actual sorted word has two groups.
example : ([1,2,1] : List ℕ).splitBy (fun a b => decide (a = b)) = [[1],[2],[1]] ∧
    closeMetadataRuns (raw [9,4,2]) [1,2,1] = raw [] ∧
    (compute [1,2,1]).sortedKeys.splitBy (fun a b => decide (a = b)) = [[1,1],[2]] := by
  refine ⟨by decide +kernel,rfl,?_⟩
  simp [compute,Cslib.AdjacentSortTrace.insert,List.range_succ,List.splitBy,List.splitBy.loop]

private def colliding : State Unit := ⟨[⟨(),[9,4,2]⟩],[9,4,2,9],⟨[]⟩⟩

-- The second group changes the EARLIER hidden representative9 to2 globally.
example : (closeMetadataRuns colliding [1,1,2,2]).body = [⟨(),[2,2,2]⟩] ∧
    (closeMetadataRuns colliding [1,1,2,2]).ports = [] ∧
    (closeMetadataRuns colliding [1,1,2,2]).rotation.successor.length = 6 := by decide +kernel

private def different (z : ℕ) : Bool := decide (z=4)

-- Output/all-name agreement alone does not force source equality, even after ALL groups.
example : (∃ τ : ℕ → Bool, (closeMetadataRuns (raw [9,4]) [1,1]).body.eval nearSem τ = true ∧
      ∀ z,τ z = different z) ∧ different 9 ≠ different 4 := by
  exact ⟨⟨different,rfl,fun _ => rfl⟩,by decide +kernel⟩

example (table : List ℕ) : closeMetadataRuns (raw [] table) [] = raw [] table := rfl
example : closeMetadataRuns (raw [] [2^300,7,5]) [] = raw [] [2^300,7,5] := rfl
example : sortAndCloseMetadataRuns g w (raw [] [2^300,7,5]) [2^300,0] = raw [] [2^300,7,5] := rfl
example : sortAndCloseMetadataRuns g w (raw [9] [2^300,7,5]) [2^300,0] = raw [9] [2^300,7,5] := rfl

-- A singleton aligned run really restricts the table once, instead of returning raw input.
example : closeMetadataRuns (⟨[⟨(),[9]⟩],[9],⟨[2^300]⟩⟩ : State Unit) [2^300] =
  ⟨[⟨(),[9]⟩],[],⟨[0,0]⟩⟩ := by
  have hpow : (2^300 : ℕ) = 2^150 * 2^150 := by decide +kernel
  conv_lhs => arg 1; arg 3; arg 1; arg 1; rw [hpow]
  conv_lhs => arg 2; arg 1; rw [hpow]
  rfl

example : (closeMetadataRuns (raw [2^250,9,2^250,9] [2^300]) [2^300,2^300,0,0]).ports = [] := by
  have h := (fields_closeMetadataRuns (raw [2^250,9,2^250,9] [2^300])
    [2^300,2^300,0,0] rfl).2.1
  exact h

private def closed : State Unit :=
  ⟨[⟨(),[]⟩,⟨(),[]⟩],[9,4],⟨[2^300,7,5]⟩⟩

example : (closeMetadataRuns closed [1,1]).body = closed.body ∧
    (closeMetadataRuns closed [1,1]).body.eval (fun _ _ => false) (fun _ => false) = false := by
  decide +kernel

example : ¬(closeMetadataRuns closed [1,1]).body.WellFormed (fun _ => 1) ∧
    (closeMetadataRuns closed [1,1]).body.eval (fun _ _ => true) (fun _ => false) = true := by
  decide +kernel

example : (closeMetadataRuns colliding [1,1,2,2]).body.WellFormed (fun _ => 3) ↔
    colliding.body.WellFormed (fun _ => 3) :=
  wellFormed_closeMetadataRuns_iff _ _ _

example : closeMetadataRuns (⟨[],[9,4],⟨[]⟩⟩ : State Empty) [0,0] = ⟨[],[],⟨[]⟩⟩ := by rfl

example {Rel : Type} (encRel : Rel ↪ List Bool) (p : State Rel × List ℕ) :
    encStateMetadata encRel p = encPair (encState encRel) (encList encNat) p := rfl

example {Rel : Type} (_encRel : Rel ↪ List Bool) (p : State Rel × List ℕ) :
    (closeMetadataRuns p.1 p.2).body = (State.body (closeMetadataRuns p.1 p.2)) := rfl

/-- No finite target instance or raw validity/entry-bound provider is needed. -/
theorem arbitrary_raw_runtime {Rel : Type} (encRel : Rel ↪ List Bool) :
    ComputableInPolyTime (fun p : State Rel × List ℕ => closeMetadataRuns p.1 p.2)
      (encStateMetadata encRel) (encState encRel) :=
  computableInPolyTime_closeMetadataRuns encRel

/-- The actual generic alphabet and fixed actual gadget remain outside runtime. -/
theorem arbitrary_composite_runtime {Rel : Type} {ar : Rel → ℕ}
    {sem : Rel → List Bool → Bool} (g : PPGadget ar sem cross) (w : GadgetWitness g)
    (encRel : Rel ↪ List Bool) :
    ComputableInPolyTime (fun p : State Rel × List ℕ => sortAndCloseMetadataRuns g w p.1 p.2)
      (encStateMetadata encRel) (encState encRel) :=
  computableInPolyTime_sortAndCloseMetadataRuns g w encRel

example {Rel : Type} (encRel : Rel ↪ List Bool) :
    ComputableInPolyTime (fun p : State Rel × List ℕ => (closeMetadataRuns p.1 p.2).ports)
      (encStateMetadata encRel) (encList encNat) :=
  encState_ports_polyTime encRel (computableInPolyTime_closeMetadataRuns encRel)

example {Rel : Type} {ar : Rel → ℕ} {sem : Rel → List Bool → Bool}
    (g : PPGadget ar sem cross) (w : GadgetWitness g) (encRel : Rel ↪ List Bool) :
    ComputableInPolyTime
      (fun p : State Rel × List ℕ => (sortAndCloseMetadataRuns g w p.1 p.2).rotation)
      (encStateMetadata encRel) Graph.encRotationCertificate :=
  encState_rotation_polyTime encRel (computableInPolyTime_sortAndCloseMetadataRuns g w encRel)

-- Primitive counts come from the public ACTUAL-prefix partition theorem.
example :
    let J := sortBoundaryMetadata g w atom keys
    let sorted : List ℕ := [1,1,2,2]
    let states := fun s => (fun J : State Unit => closeFirstMetadataRun J
      (sorted.drop (sorted.length-J.ports.length)))^[s] J
    let blocks := ((List.range sorted.length).map (fun s =>
      (sorted.drop (sorted.length-(states s).ports.length)).takeWhile
        (fun b => decide (b = (sorted.drop (sorted.length-(states s).ports.length)).headD
          0)))).filter
          (fun xs => decide (xs ≠ []))
    let F := ((List.range sorted.length).map (fun s =>
      ((sorted.drop (sorted.length-(states s).ports.length)).takeWhile
        (fun b => decide (b = (sorted.drop (sorted.length-(states s).ports.length)).headD
          0))).length-1)).sum
    F = 2 ∧ blocks.length = 2 := by
  let J := sortBoundaryMetadata g w atom keys
  have hp : J.ports.length=4 := by
    change (sortBoundaryMetadata g w atom keys).ports.length=4
    rw [sortBoundaryMetadata,computed_keys]
    decide +kernel
  have h := partition_closeMetadataRuns J [1,1,2,2] hp.symm
  change _ ∧ _ ∧ _=J.ports.length-2 ∧ _=2 ∧ _ at h
  exact ⟨by simpa only [hp] using h.2.2.1,h.2.2.2.1⟩

end CslibFrontierTests.CSPMetadataRuns
