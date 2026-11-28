/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.CSP.BoundaryAppend
public import CslibFrontier.Computability.Complexity.Problems.CSP.RotationSystem.BoundaryAppendAcceptance
public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.CrossoverOriginal
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Relabel
import CslibFrontier.Logics.Propositional.CSP.PrimitivePositive.Operations
import CslibFrontier.Computability.PolyTime.CSP.Vars
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Mathlib.Data.Sum.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Native disjoint insertion of an ordered CROSS

One composition step doubles every old variable name and places a fixed actual CROSS
gadget at odd names. Its four free ports, in their original directed order, follow the
old boundary. The emitted certificate is the executed ordered-boundary append program.
Repeated and sparse old names, nullary rows and closed components are retained.

The template and its ordered witness are static constants. The original-language existence
result obtains them internally from the common-complement and bad-relation premises; the
target alphabet need not be finite. Runtime covers every raw state and uses no acceptance
invariant. Assignment extension agrees on all even old names and all four odd free ports;
odd auxiliary names are existential witnesses.

This is an original composition step. Adjacent wire swaps, the iteration bound and the
common-complement native hardness reduction remain objectives of
[#3091](https://github.com/cslib-community/cslib-frontier/issues/3091).

## Main definitions

* `CrossInsertion.State`: a raw body, ordered boundary and literal successor table.
* `CrossInsertion.insert`: disjointly insert one fixed actual ordered CROSS.

## Main results

* `CrossInsertion.accepted_insert`: the computed table passes both complete checks.
* `CrossInsertion.eval_insert_iff`: exact extension semantics, including unused old names.
* `CrossInsertion.computableInPolyTime_insert`: native runtime on every raw encoded state.
* `CrossInsertion.exists_originalInsertion`: static original-language template selection.
-/

public section

namespace Cslib.Complexity.CSP.CrossInsertion

open Cslib.Logic.PL Cslib.Logic.PL.CSP Cslib.Logic.PL.CSP.Crossover
open Cslib.BitString OrderedBoundary Turing.MultiTapeTM

/-- Raw data carried by a boundary composition program; no validity proof is input data. -/
structure State (Rel : Type) where
  /-- Actual original-language constraints with binary natural-number names. -/
  body : CSP Rel ℕ
  /-- Ordered boundary positions; repeated names remain in raw inputs. -/
  ports : List ℕ
  /-- Binary successor entries on body darts followed by structural probe darts. -/
  rotation : Graph.RotationCertificate

variable {Rel : Type}

/-- Encode the binary-named body first, then the binary port word, then the binary
successor certificate. The first two fields are framed, with no extra grouping or tag. -/
enc_structure encState (encRel : Rel ↪ List Bool) : State Rel where
  body : (encCSP encRel encNat),
  ports : (encList encNat),
  rotation : Graph.encRotationCertificate

variable {ar : Rel → ℕ} {sem : Rel → List Bool → Bool}

/-- The source invariant for composition: distinct boundary names and the two full
ordered-boundary checks. This predicate is not used in the runtime certificate. -/
@[expose] def State.Accepted (I : State Rel) : Prop :=
  I.ports.Nodup ∧ OrderedBoundary.verify I.body I.ports I.rotation = true

instance (I : State Rel) : Decidable I.Accepted :=
  inferInstanceAs (Decidable (I.ports.Nodup ∧
    OrderedBoundary.verify I.body I.ports I.rotation = true))

/-- Fresh odd labels enumerate the four free ports first, followed by every actual
auxiliary of the fixed gadget. In particular the free word is `[1, 3, 5, 7]`. -/
private def oddName {k : ℕ} (v : Fin 4 ⊕ Fin k) : ℕ :=
  2 * (finSumFinEquiv v).val + 1

private theorem oddName_injective (k : ℕ) :
    Function.Injective (oddName : Fin 4 ⊕ Fin k → ℕ) := by
  intro x y h
  apply finSumFinEquiv.injective
  apply Fin.ext
  dsimp only [oddName] at h
  omega

private theorem even_ne_odd (x : ℕ) {k : ℕ} (v : Fin 4 ⊕ Fin k) :
    2 * x ≠ oddName v := by
  dsimp only [oddName]; omega

private def freePorts : List ℕ := List.ofFn (fun i : Fin 4 => 2 * i.val + 1)

private theorem mapped_freePorts (k : ℕ) :
    (List.ofFn (Sum.inl : Fin 4 → Fin 4 ⊕ Fin k)).map oddName = freePorts := by
  simp [oddName, freePorts]

private theorem disjoint_tags (xs : List ℕ) {k : ℕ} (ys : List (Fin 4 ⊕ Fin k)) :
    List.Disjoint (xs.map (2 * ·)) (ys.map oddName) := by
  refine List.disjoint_left.mpr fun _ hx hy => ?_
  obtain ⟨x, _, rfl⟩ := List.mem_map.mp hx
  obtain ⟨y, _, hy⟩ := List.mem_map.mp hy
  exact even_ne_odd x y hy.symm

variable (g : PPGadget ar sem cross) (w : GadgetWitness g)

/-- Insert a fixed CROSS at odd names after doubling all old names. The actual old body,
port lengths and static template occurrence count fund the raw append table computation. -/
@[expose] def insert (I : State Rel) : State Rel where
  body := I.body.relabel (2 * ·) ++
    g.body.relabel (fun v => 2 * (finSumFinEquiv v).val + 1)
  ports := I.ports.map (2 * ·) ++ List.ofFn (fun i : Fin 4 => 2 * i.val + 1)
  rotation := appendRawCertificate I.body.occurrences.length I.ports.length
    g.body.occurrences.length 4 I.rotation w.certificate

/-- Insertion adds exactly the actual template rows. No row is removed, including nullaries. -/
@[simp] theorem length_insert_body (I : State Rel) :
    (insert g w I).body.length = I.body.length + g.body.length := by
  simp [insert, CSP.relabel]

/-- Every old occurrence remains, followed by every actual template occurrence. -/
@[simp] theorem length_insert_occurrences (I : State Rel) :
    (insert g w I).body.occurrences.length =
      I.body.occurrences.length + g.body.occurrences.length := by
  simp [insert, CSP.length_occurrences, CSP.relabel, Constraint.relabel,
    List.map_map, Function.comp_def, List.sum_append]

/-- Four original directed free ports are appended, without deduplicating old positions. -/
@[simp] theorem length_insert_ports (I : State Rel) :
    (insert g w I).ports.length = I.ports.length + 4 := by
  simp [insert]

/-- The raw emitted table has the actual combined dart count, even on malformed inputs. -/
@[simp] theorem length_insert_rotation (I : State Rel) :
    (insert g w I).rotation.successor.length =
      2 * (I.body.occurrences.length + I.ports.length + g.body.occurrences.length + 4) :=
  length_appendRawCertificate _ _ _ _ _ _

/-- The actual gadget supplies every new arity obligation; old malformed rows stay malformed. -/
theorem wellFormed_insert_iff (I : State Rel) :
    (insert g w I).body.WellFormed ar ↔ I.body.WellFormed ar := by
  refine ⟨fun h c hc => ?_, fun h c hc => ?_⟩
  · simpa only [Constraint.relabel, List.length_map] using
      h (c.relabel (2 * ·)) (List.mem_append_left _ (List.mem_map.mpr ⟨c, hc, rfl⟩))
  · exact (List.mem_append.mp hc).elim (h.relabel (2 * ·) c) (g.wellFormed.relabel oddName c)

/-- Insertion preserves distinctness exactly, without silently repairing repeated ports. -/
theorem nodup_insert_ports_iff (I : State Rel) :
    (insert g w I).ports.Nodup ↔ I.ports.Nodup := by
  refine ⟨fun h => h.of_append_left.of_map (2 * ·), fun h => List.nodup_append'.mpr
    ⟨h.map (mul_right_injective₀ (by decide)), ?_, ?_⟩⟩
  · refine List.nodup_ofFn.mpr fun i j hij => Fin.ext ?_
    change 2 * i.val + 1 = 2 * j.val + 1 at hij
    omega
  · simpa only [mapped_freePorts, freePorts] using
      disjoint_tags I.ports (List.ofFn (Sum.inl : Fin 4 → Fin 4 ⊕ Fin g.numAux))

/-- Both complete checks for the emitted table follow from the actual relabeled static
gadget and `Witness.appendComputed`. Empty old boundaries and closed components survive. -/
theorem accepted_insert (I : State Rel) (hI : I.Accepted) : (insert g w I).Accepted := by
  let old : Witness I.body I.ports := ⟨I.rotation, hI.2⟩
  let left := old.relabel (2 * ·) fun _ _ _ _ h => Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) h
  let right := w.relabel oddName fun _ _ _ _ h => oddName_injective _ h
  have hd : List.Disjoint ((I.body.relabel (2 * ·)).vars ++ I.ports.map (2 * ·))
      ((g.body.relabel oddName).vars ++
        (List.ofFn (Sum.inl : Fin 4 → Fin 4 ⊕ Fin g.numAux)).map oddName) := by
    rw [CSP.vars_relabel, CSP.vars_relabel, ← List.map_append, ← List.map_append]
    exact disjoint_tags _ _
  have hn : (I.ports.map (2 * ·) ++
      (List.ofFn (Sum.inl : Fin 4 → Fin 4 ⊕ Fin g.numAux)).map oddName).Nodup := by
    rw [mapped_freePorts]
    exact (nodup_insert_ports_iff g w I).mpr hI.1
  have h := (left.appendComputed right hd hn).accepted
  change OrderedBoundary.verify (I.body.relabel (2 * ·) ++ g.body.relabel oddName)
    (I.ports.map (2 * ·) ++ (List.ofFn (Sum.inl : Fin 4 →
      Fin 4 ⊕ Fin g.numAux)).map oddName)
    (appendRawCertificate (I.body.relabel (2 * ·)).occurrences.length
      (I.ports.map (2 * ·)).length (g.body.relabel oddName).occurrences.length
      ((List.ofFn (Sum.inl : Fin 4 → Fin 4 ⊕ Fin g.numAux)).map oddName).length
      I.rotation w.certificate) = true at h
  simp only [CSP.occurrences_relabel, List.length_map, List.length_ofFn,
    mapped_freePorts, freePorts] at h
  exact ⟨(nodup_insert_ports_iff g w I).mpr hI.1, h⟩

private theorem combinedName_injective (k : ℕ) :
    Function.Injective (Sum.elim (fun x : ℕ => 2 * x)
      (oddName : Fin 4 ⊕ Fin k → ℕ)) :=
  (mul_right_injective₀ (by decide : (2 : ℕ) ≠ 0)).sumElim
    (oddName_injective k) (fun x v => even_ne_odd x v)

/-- Exact composition semantics. The extension agrees with the assignment on ALL even
old names and with the four given odd free ports. Odd auxiliary labels are internal witnesses;
there is no source acceptance, well-formedness or prefix hypothesis. -/
theorem eval_insert_iff (I : State Rel) (σ : ℕ → Bool) (a : Fin 4 → Bool) :
    I.body.eval sem σ = true ∧ a ∈ cross ↔
      ∃ τ : ℕ → Bool, (insert g w I).body.eval sem τ = true ∧
        (∀ x, τ (2 * x) = σ x) ∧ (∀ i : Fin 4, τ (2 * i.val + 1) = a i) := by
  classical
  have heval (τ : ℕ → Bool) : (insert g w I).body.eval sem τ = true ↔
      I.body.eval sem (τ ∘ (2 * ·)) = true ∧
        g.body.eval sem (τ ∘ oddName) = true := by
    simp only [insert, CSP.eval, CSP.relabel, List.all_append, List.all_map,
      Function.comp_def, Constraint.eval_relabel, Bool.and_eq_true, oddName]
  constructor
  · rintro ⟨hσ, ha⟩
    obtain ⟨b, hb⟩ := (g.correct a).mp ha
    let f := Sum.elim (fun x : ℕ => 2 * x) (oddName : Fin 4 ⊕ Fin g.numAux → ℕ)
    let values := Sum.elim σ (Sum.elim a b)
    let τ := Function.extend f values fun _ => false
    have ht (x) : τ (f x) = values x :=
      (combinedName_injective g.numAux).extend_apply values (fun _ => false) x
    refine ⟨τ, (heval τ).mpr
      ⟨by simpa only [show τ ∘ (2 * ·) = σ from funext fun x => ht (.inl x)] using hσ,
        by simpa only [show τ ∘ oddName = Sum.elim a b from funext fun v => ht (.inr v)] using hb⟩,
      fun x => ht (.inl x), fun i => ?_⟩
    simpa only [f, values, oddName, finSumFinEquiv_apply_left, Fin.val_castAdd, Sum.elim_inl,
      Sum.elim_inr] using ht (.inr (.inl i))
  · rintro ⟨τ, hτ, hold, hfree⟩
    obtain ⟨hσ, hb⟩ := (heval τ).mp hτ
    refine ⟨by simpa only [show τ ∘ (2 * ·) = σ from funext hold] using hσ,
      (g.correct a).mpr ⟨fun j => τ (oddName (.inr j)), ?_⟩⟩
    convert hb using 2
    exact funext fun | .inl i => (hfree i).symm | .inr _ => rfl

/-- Doubling a positive old name adds exactly one binary digit. Zero stays the empty word.
This is a single-step identity; accumulated bounds for a later iteration are separate. -/
theorem length_evenName (x : ℕ) (hx : x ≠ 0) :
    (encNat (2 * x)).length = (encNat x).length + 1 := by
  rw [encNat_apply, encNat_apply, Nat.bit0_bits x hx, List.length_cons]

/-- One fixed insertion is native polynomial time on EVERY raw state, with binary names,
ports and table entries. Only list lengths fund loops; no source invariant is used. -/
theorem computableInPolyTime_insert (encRel : Rel ↪ List Bool) :
    ComputableInPolyTime (insert g w) (encState encRel) (encState encRel) := by
  open scoped State in
  have hbodytag : ComputableInPolyTime (fun I : State Rel => I.body.relabel (2 * ·))
      (encState encRel) (encCSP encRel encNat) := by
    unfold CSP.relabel Constraint.relabel
    fun_prop
  have hM : ComputableInPolyTime (fun I : State Rel => I.body.occurrences.length)
      (encState encRel) encUnary := by
    simpa only [Function.comp_def, CSP.vars_length_eq_occurrences] using
      (computableInPolyTime_length_vars encRel encNat).comp (by fun_prop)
  have htable := computableInPolyTime_appendRawCertificate
    (leftBody := fun I : State Rel => I.body.occurrences.length)
    (leftPorts := fun I : State Rel => I.ports.length)
    (left := State.rotation (Rel := Rel))
    hM (by fun_prop) (.const g.body.occurrences.length) (.const 4) (by fun_prop)
    (.const w.certificate)
  unfold insert
  exact encState_mk_polyTime encRel (by fun_prop) (by fun_prop) htable

/-- The common-complement/bad-original-relation premises internally yield a static actual
CROSS insertion with its all-raw native runtime, full checker preservation and exact assignment
extension. This is one disjoint composition step, not an adjacent swap or a hardness theorem. -/
theorem exists_originalInsertion (encRel : Rel ↪ List Bool)
    (h : ¬HasSchaeferPolymorphism ar sem)
    (hnot : HasPolymorphism ar sem (fun a : Fin 1 → Bool => !(a 0)))
    (r : Rel) (hne : (booleanRelation ar sem r).Nonempty)
    (hbad : ¬IsEvenDeltaMatroid (cyclicDifferenceRelation (booleanRelation ar sem r))) :
    ∃ (g : PPGadget ar sem cross) (w : GadgetWitness g),
      ComputableInPolyTime (insert g w) (encState encRel) (encState encRel) ∧
      (∀ I, I.Accepted → (insert g w I).Accepted) ∧
      ∀ (I : State Rel) (σ : ℕ → Bool) (a : Fin 4 → Bool),
        I.body.eval sem σ = true ∧ a ∈ cross ↔
          ∃ τ : ℕ → Bool, (insert g w I).body.eval sem τ = true ∧
            (∀ x, τ (2 * x) = σ x) ∧ (∀ i : Fin 4, τ (2 * i.val + 1) = a i) := by
  obtain ⟨g, ⟨w⟩⟩ := exists_orderedCrossGadget h hnot r hne hbad
  exact ⟨g, w, computableInPolyTime_insert g w encRel, accepted_insert g w,
    eval_insert_iff g w⟩

end Cslib.Complexity.CSP.CrossInsertion
