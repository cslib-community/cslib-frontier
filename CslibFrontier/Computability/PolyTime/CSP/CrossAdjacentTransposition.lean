/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.CSP.CrossTailTransposition
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeLoops
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List.Size
import CslibFrontier.Foundations.Data.Nat.BinarySize
import Mathlib.Data.List.Rotate
import CslibFrontier.Tactic.EncLen
import Mathlib.Data.List.GetD
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation
import CslibFrontier.Foundations.Data.Nat.Bits

/-!
# A bounded positioned adjacent value transposition

`CrossInsertion.transposeAdjacent` moves the suffix past the selected pair by actual RIGHT
calls, executes the existing CROSS tail program, then moves the suffix back by actual LEFT
calls. Invalid binary positions retain the ENTIRE input before insertion. The selected values
are exchanged at fresh names, not by permuting the original names. Raw cycles are never canceled.

This original routing step toward [#3091](https://github.com/cslib-community/cslib-frontier/issues/3091)
uses one fixed actual gadget and its witness outside runtime. Sorting schedules, accumulated
swap bounds, the native planarization compiler and full hardness remain open there.

## Main definitions

* `CrossInsertion.transposeAdjacent`: the guarded executed routing program.

## Main results

* `CrossInsertion.ports_transposeAdjacent`: the exact directed output word.
* `CrossInsertion.accepted_transposeAdjacent`: full checker preservation internally.
* `CrossInsertion.recover_transposeAdjacent`: source satisfaction and exact swapped values.
* `CrossInsertion.eval_transposeAdjacent_iff`: extension on every old even name.
* `CrossInsertion.wellFormed_transposeAdjacent_iff`: exact arity on all raw inputs.
* `CrossInsertion.computableInPolyTime_transposeAdjacent`: plain all-raw runtime.
-/

public section

namespace Cslib.Complexity.CSP.CrossInsertion

open Cslib.Logic.PL Cslib.Logic.PL.CSP Cslib.Logic.PL.CSP.Crossover
open OrderedBoundary Graph Cslib.BitString Turing.MultiTapeTM

variable {Rel : Type} {ar : Rel → ℕ} {sem : Rel → List Bool → Bool}
variable (g : PPGadget ar sem cross) (w : GadgetWitness g)

/-- Select positions `j,j+1` using a binary index. The suffix length funds both literal
rotation loops. Invalid positions preserve the entire raw input before insertion. -/
@[expose] def transposeAdjacent (I : State Rel) (j : ℕ) : State Rel :=
  if j + 1 < I.ports.length then
    let r := I.ports.length - (j + 2)
    (rotateLeft^[r]) (transposeTail g w ((rotateRight^[r]) I))
  else I

/-- Out-of-range binary positions preserve every row, name and raw table entry. -/
theorem transposeAdjacent_invalid (I : State Rel) (j : ℕ)
    (h : I.ports.length ≤ j + 1) : transposeAdjacent g w I j = I := by
  rw [transposeAdjacent, ite_eq_right (not_lt.mpr h)]

private theorem left_body (I : State Rel) (n : ℕ) :
    ((rotateLeft^[n]) I).body = I.body := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', rotateLeft_body, ih]

private theorem right_body (I : State Rel) (n : ℕ) :
    ((rotateRight^[n]) I).body = I.body := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', rotateRight_body, ih]

private theorem left_ports (I : State Rel) (n : ℕ) :
    ((rotateLeft^[n]) I).ports = I.ports.rotate n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', rotateLeft_ports, ih, List.rotate_rotate]

private theorem right_ports (I : State Rel) (n : ℕ) :
    ((rotateRight^[n]) I).ports = (I.ports.reverse.rotate n).reverse := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', rotateRight_ports, ih]
    simp only [List.reverse_reverse, List.rotate_rotate]

private theorem left_accepted (I : State Rel) (n : ℕ) (h : I.Accepted) :
    ((rotateLeft^[n]) I).Accepted := by
  induction n with
  | zero => exact h
  | succ n ih => exact Function.iterate_succ_apply' _ _ _ ▸ accepted_rotateLeft _ ih

private theorem right_accepted (I : State Rel) (n : ℕ) (h : I.Accepted) :
    ((rotateRight^[n]) I).Accepted := by
  induction n with
  | zero => exact h
  | succ n ih => exact Function.iterate_succ_apply' _ _ _ ▸ accepted_rotateRight _ ih

/-- Every table check is derived from actual preceding accepted output, including both loops. -/
theorem accepted_transposeAdjacent (I : State Rel) (j : ℕ) (h : I.Accepted) :
    (transposeAdjacent g w I j).Accepted := by
  unfold transposeAdjacent
  split_ifs
  · exact left_accepted _ _ (accepted_transposeTail g w _ (right_accepted I _ h))
  · exact h

-- The initial positioned RIGHT-state calculation is independent of any gadget.
private theorem positioned_state (F : CSP Rel ℕ) (L : List ℕ) (x y : ℕ)
    (R : List ℕ) (c : RotationCertificate) :
    (rotateRight^[R.length]) (⟨F, L ++ [x, y] ++ R, c⟩ : State Rel) =
      ⟨F, (R ++ L) ++ [x, y],
        ((rotateRight^[R.length]) (⟨F, L ++ [x, y] ++ R, c⟩ : State Rel)).rotation⟩ := by
  let I : State Rel := ⟨F, L ++ [x, y] ++ R, c⟩
  let J := (rotateRight^[R.length]) I
  have hJ : J.ports = (R ++ L) ++ [x, y] := by
    rw [right_ports]
    simp only [I, List.reverse_append]
    rw [← List.length_reverse (as := R), List.rotate_append_length_eq]
    simp only [List.reverse_reverse, List.reverse_append, List.append_assoc]
  have hb : J.body = F := right_body I R.length
  calc
    J = ⟨J.body, J.ports, J.rotation⟩ := rfl
    _ = _ := by rw [hb, hJ]

private theorem positioned_fields (F : CSP Rel ℕ) (L : List ℕ) (x y : ℕ)
    (R : List ℕ) (c : RotationCertificate) :
    let I : State Rel := ⟨F, L ++ [x, y] ++ R, c⟩
    let J := (rotateRight^[R.length]) I
    (transposeAdjacent g w I L.length).body = (transposeTail g w J).body ∧
    J.body = F ∧ J.ports = R ++ L ++ [x, y] ∧
    (transposeAdjacent g w I L.length).ports =
      L.map (2 * ·) ++ [5, 7] ++ R.map (2 * ·) := by
  intro I J
  have hstate := positioned_state F L x y R c
  have hvalid : L.length + 1 < I.ports.length := by simp [I]
  have hr : I.ports.length - (L.length + 2) = R.length := by simp [I]; omega
  have hp := ports_transposeTail g w F (R ++ L) x y J.rotation
  rw [← hstate] at hp
  rw [transposeAdjacent, ite_eq_left hvalid, hr]
  refine ⟨left_body _ _, right_body I _, congrArg State.ports hstate, ?_⟩
  rw [left_ports, hp, List.map_append, ← List.length_map (f := (2 * ·)), List.append_assoc,
    List.rotate_append_length_eq]

/-- The actual directed port word has fresh middle names carrying reversed values.
Repeated names and malformed tables need no premise. -/
theorem ports_transposeAdjacent (F : CSP Rel ℕ) (L : List ℕ) (x y : ℕ)
    (R : List ℕ) (c : RotationCertificate) :
    (transposeAdjacent g w (⟨F, L ++ [x, y] ++ R, c⟩ : State Rel) L.length).ports =
      L.map (2 * ·) ++ [5, 7] ++ R.map (2 * ·) :=
  (positioned_fields g w F L x y R c).2.2.2

/-- A tail position executes exactly the old tail primitive, including its complete table. -/
theorem transposeAdjacent_tail (F : CSP Rel ℕ) (L : List ℕ) (x y : ℕ)
    (c : RotationCertificate) :
    transposeAdjacent g w (⟨F, L ++ [x, y], c⟩ : State Rel) L.length =
      transposeTail g w ⟨F, L ++ [x, y], c⟩ := by
  simp [transposeAdjacent]

/-- Recover the source assignment on EVERY old even name from one satisfying output,
and recover the complete directed swapped word. No checker or syntax premise is needed. -/
theorem recover_transposeAdjacent (F : CSP Rel ℕ) (L : List ℕ) (x y : ℕ)
    (R : List ℕ) (c : RotationCertificate) (τ : ℕ → Bool)
    (ht : (transposeAdjacent g w (⟨F, L ++ [x, y] ++ R, c⟩ : State Rel)
      L.length).body.eval sem τ = true) :
    F.eval sem (fun z => τ (2 * z)) = true ∧
      (transposeAdjacent g w (⟨F, L ++ [x, y] ++ R, c⟩ : State Rel)
        L.length).ports.map τ =
        L.map (fun z => τ (2 * z)) ++ [τ (2 * y), τ (2 * x)] ++
          R.map (fun z => τ (2 * z)) := by
  let I : State Rel := ⟨F, L ++ [x, y] ++ R, c⟩
  let J := (rotateRight^[R.length]) I
  have hf := positioned_fields g w F L x y R c
  have hj := positioned_state F L x y R c
  obtain ⟨hrec1, hrec2⟩ := recover_transposeTail g w F (R ++ L) x y J.rotation τ
    (by rwa [← hj, ← hf.1])
  rw [ports_transposeTail, List.map_append, List.map_map] at hrec2
  obtain ⟨h5, h7⟩ : τ 5 = τ (2 * y) ∧ τ 7 = τ (2 * x) := by
    simpa using List.append_cancel_left hrec2
  refine ⟨hrec1, ?_⟩
  simpa [Function.comp_def, h5, h7] using
    congrArg (List.map τ) (ports_transposeAdjacent g w F L x y R c)

/-- Exact extension at a valid selected pair. The fresh output word carries `y,x`, and
all old even names, including unused names, agree with the original assignment. -/
theorem eval_transposeAdjacent_iff (F : CSP Rel ℕ) (L : List ℕ) (x y : ℕ)
    (R : List ℕ) (c : RotationCertificate) (σ : ℕ → Bool) :
    F.eval sem σ = true ↔ ∃ τ : ℕ → Bool,
      (transposeAdjacent g w (⟨F, L ++ [x, y] ++ R, c⟩ : State Rel)
        L.length).body.eval sem τ = true ∧
      (∀ z, τ (2 * z) = σ z) ∧
      (transposeAdjacent g w (⟨F, L ++ [x, y] ++ R, c⟩ : State Rel)
        L.length).ports.map τ = L.map σ ++ [σ y, σ x] ++ R.map σ := by
  let I : State Rel := ⟨F, L ++ [x, y] ++ R, c⟩
  let J := (rotateRight^[R.length]) I
  have hf := positioned_fields g w F L x y R c
  have hj := positioned_state F L x y R c
  constructor
  · intro hσ
    obtain ⟨τ, ht, he, _⟩ := (eval_transposeTail_iff g w F (R ++ L) x y J.rotation σ).mp hσ
    have hout : (transposeAdjacent g w I L.length).body.eval sem τ = true := by rwa [hf.1, hj]
    refine ⟨τ, hout, he, ?_⟩
    simpa only [funext he, he] using (recover_transposeAdjacent g w F L x y R c τ hout).2
  · rintro ⟨τ, ht, he, _⟩
    simpa only [funext he] using (recover_transposeAdjacent g w F L x y R c τ ht).1

/-- Wrong-arity old constraints stay wrong-arity; the actual CROSS supplies the new scopes. -/
theorem wellFormed_transposeAdjacent_iff (I : State Rel) (j : ℕ) :
    (transposeAdjacent g w I j).body.WellFormed ar ↔ I.body.WellFormed ar := by
  unfold transposeAdjacent
  split_ifs <;> simp [left_body, wellFormed_transposeTail_iff, right_body]

/-- Rows, occurrences and port counts for a valid positioned operation. These are
one-operation bounds, not an accumulated routing/iteration certificate. -/
private theorem counts_valid (F : CSP Rel ℕ) (L : List ℕ) (x y : ℕ)
    (R : List ℕ) (c : RotationCertificate) :
    let K := transposeAdjacent g w (⟨F, L ++ [x, y] ++ R, c⟩ : State Rel) L.length
    K.body.length = F.length + g.body.length ∧
    K.body.occurrences.length = F.occurrences.length + g.body.occurrences.length ∧
    K.ports.length = L.length + 2 + R.length := by
  have hf := positioned_fields g w F L x y R c
  have hj := positioned_state F L x y R c
  refine ⟨by rw [hf.1, hj, length_transposeTail_body],
    by rw [hf.1, hj, length_transposeTail_occurrences], ?_⟩
  rw [ports_transposeAdjacent]
  simp only [List.length_append, List.length_map, List.length_cons, List.length_nil]

private theorem split_valid (I : State Rel) (j : ℕ) (h : j + 1 < I.ports.length) :
    ∃ L x y R, L.length = j ∧ I = (⟨I.body, L ++ [x, y] ++ R, I.rotation⟩ : State Rel) := by
  have hj : j < I.ports.length := by omega
  refine ⟨I.ports.take j, I.ports[j], I.ports[j+1], I.ports.drop (j+2), ?_, ?_⟩
  · exact List.length_take_of_le hj.le
  · simp [List.append_assoc]

/-- Total raw component counts. Only a successful guard inserts the actual gadget;
invalid requests preserve every component and never change the boundary length. -/
theorem counts_transposeAdjacent (I : State Rel) (j : ℕ) :
    let e := if j + 1 < I.ports.length then 1 else 0
    (transposeAdjacent g w I j).body.length = I.body.length + e * g.body.length ∧
    (transposeAdjacent g w I j).body.occurrences.length =
      I.body.occurrences.length + e * g.body.occurrences.length ∧
    (transposeAdjacent g w I j).ports.length = I.ports.length := by
  dsimp only
  by_cases h : j + 1 < I.ports.length
  · obtain ⟨L, x, y, R, hL, hI⟩ := split_valid I j h
    have hc := counts_valid g w I.body L x y R I.rotation
    have hp : I.ports.length = j + 2 + R.length := by
      simpa only [List.length_append, List.length_cons, List.length_nil, hL] using
        congrArg (fun S => S.ports.length) hI
    rw [hL, ← hI] at hc
    simpa only [ite_eq_left h, one_mul, ← hp] using hc
  · simp [transposeAdjacent, h]

/-- Each successful request appends the fixed template's relation-symbol word after all
old rows; invalid requests preserve the word exactly. This includes arbitrary encoded Rel. -/
theorem relations_transposeAdjacent (I : State Rel) (j : ℕ) :
    (transposeAdjacent g w I j).body.map Constraint.rel = I.body.map Constraint.rel ++
      (if j + 1 < I.ports.length then g.body.map Constraint.rel else []) := by
  by_cases h : j + 1 < I.ports.length
  · have hlt2 : ¬I.ports.length < 2 := by omega
    rw [transposeAdjacent, ite_eq_left h, left_body, relations_transposeTail, right_body,
      right_ports]
    simp [hlt2, h]
  · rw [transposeAdjacent_invalid g w I j (not_lt.mp h), ite_eq_right h, List.append_nil]

/-- One positioned operation adds at most one bit to old names. Rotations preserve
name multisets; no accumulated repeated-swap bound is asserted. -/
theorem name_width_transposeAdjacent_le (F : CSP Rel ℕ) (L : List ℕ) (x y : ℕ)
    (R : List ℕ) (c : RotationCertificate) (W : ℕ)
    (hW : ∀ z ∈ F.vars ++ (L ++ [x, y] ++ R), z.size ≤ W) :
    ∀ z ∈ (transposeAdjacent g w (⟨F, L ++ [x, y] ++ R, c⟩ : State Rel)
      L.length).body.vars ++
        (transposeAdjacent g w (⟨F, L ++ [x, y] ++ R, c⟩ : State Rel) L.length).ports,
      z.size ≤ max (W + 1) (2 * g.numAux + 7).size := by
  let I : State Rel := ⟨F, L ++ [x, y] ++ R, c⟩
  let J := (rotateRight^[R.length]) I
  have hf := positioned_fields g w F L x y R c
  have hj := positioned_state F L x y R c
  have hW' : ∀ z ∈ F.vars ++ ((R ++ L) ++ [x, y]), z.size ≤ W := fun z hz =>
    hW z (by simpa only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      or_assoc, or_left_comm, or_comm] using hz)
  intro z hz
  rw [hf.1, hj, ports_transposeAdjacent] at hz
  refine name_width_transposeTail_le g w F (R ++ L) x y J.rotation W hW' z ?_
  simpa only [ports_transposeTail, List.map_append, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, or_assoc, or_left_comm, or_comm] using hz

-- The two offset loops are implementation details, with actual State steps throughout.
private def turn (right : Bool) (I : State Rel) : State Rel :=
  if right then rotateRight I else rotateLeft I

private theorem turn_body (b : Bool) (I : State Rel) : (turn b I).body = I.body := by
  cases b <;> simp only [turn, Bool.false_eq_true, ↓reduceIte, rotateLeft_body,
    rotateRight_body]

private theorem turn_ports_perm (b : Bool) (I : State Rel) :
    (turn b I).ports.Perm I.ports := by
  cases b
  · exact (rotateLeft_ports I).symm ▸ List.rotate_perm _ _
  · exact (rotateRight_ports I).symm ▸
      (List.reverse_perm _).trans ((List.rotate_perm _ _).trans (List.reverse_perm _))

private theorem turn_table (b : Bool) (I : State Rel) (B : ℕ)
    (he : ∀ v ∈ I.rotation.successor, v.size ≤ B)
    (hd : (2 * (I.body.occurrences.length + I.ports.length)).size ≤ B) :
    (turn b I).rotation.successor.length ≤
      max I.rotation.successor.length (2 * (I.body.occurrences.length + I.ports.length)) ∧
    ∀ v ∈ (turn b I).rotation.successor, v.size ≤ B := by
  rcases I with ⟨F, ports, c⟩
  match ports with
  | [] | [_] =>
    simp only [turn, rotateLeft, rotateRight, ite_self]
    exact ⟨le_max_left _ _, he⟩
  | x :: y :: ps =>
    let N := (x :: y :: ps).length
    let M := F.occurrences.length
    have hlen1 : ¬(x :: y :: ps).length ≤ 1 := by simp
    have hread (i : ℕ) : (c.successor.getD i 0).size ≤ B := by
      by_cases hi : i < c.successor.length
      · simpa only [List.getD_eq_getElem _ _ hi] using he _ (List.getElem_mem hi)
      · simp [not_lt.mp hi]
    have hentry (shift : ℕ → ℕ) (hs : ∀ j, shift j < N) (i : ℕ) :
        (boundaryIndexMap M N shift (c.successor.getD i 0)).size ≤ B :=
      (size_boundaryIndexMap_le M N shift hs _).trans (max_le (hread i) hd)
    cases b <;>
      simp only [turn, Bool.false_eq_true, ↓reduceIte, rotateLeft, rotateRight,
        rotateBoundaryCertificate, rotateBoundaryCertificateRight_eq_reindex_mod,
        hlen1, ↓reduceIte]
    all_goals
      refine ⟨(RotationCertificate.length_reindex _ _ _ _).trans_le (le_max_right _ _),
        fun v hv => ?_⟩
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hv
      exact hentry _ (fun _ => Nat.mod_lt _ (Nat.succ_pos _)) _

private theorem enc_ports_perm {xs ys : List ℕ} (h : xs.Perm ys) :
    (encList encNat xs).length = (encList encNat ys).length :=
  (h.flatMap_right (frame ∘ encNat)).length_eq

private theorem loop_components (encRel : Rel ↪ List Bool) (b : Bool) (I : State Rel) (n : ℕ) :
    ((turn b)^[n] I).body = I.body ∧
    ((turn b)^[n] I).ports.Perm I.ports ∧
    ((turn b)^[n] I).rotation.successor.length ≤
      max I.rotation.successor.length (2 * (I.body.occurrences.length + I.ports.length)) ∧
    ∀ v ∈ ((turn b)^[n] I).rotation.successor,
      v.size ≤ (encState encRel I).length +
        2 * (I.body.occurrences.length + I.ports.length) := by
  induction n with
  | zero =>
    refine ⟨rfl, .refl _, le_max_left _ _, ?_⟩
    intro v hv
    have := SizedListEncoding.length_elem_le (encA := encNat) (encL := encList encNat)
      I.rotation.successor v hv
    rw [encNat_apply, Nat.size_eq_bits_len] at this
    enc_len [encState_apply, encStateFields, Graph.encRotationCertificate_apply,
      Graph.encRotationCertificateFields] at *
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have hp := ih.2.1.length_eq
    have hd : (2 * (((turn b)^[n] I).body.occurrences.length +
        ((turn b)^[n] I).ports.length)).size ≤
        (encState encRel I).length +
          2 * (I.body.occurrences.length + I.ports.length) := by
      rw [ih.1, hp]
      exact (Nat.size_le_self _).trans (Nat.le_add_left _ _)
    have htab := turn_table b ((turn b)^[n] I) _ ih.2.2.2 hd
    refine ⟨(turn_body _ _).trans ih.1, (turn_ports_perm _ _).trans ih.2.1, ?_, htab.2⟩
    rw [ih.1, hp] at htab
    exact htab.1.trans (max_le ih.2.2.1 (le_max_right _ _))

-- S retains the complete original encoded body and port payload: relation symbols,
-- row/scope framing, repeated binary names and unused ports are charged exactly once.
-- During a rotation loop Q/M/P and body/port name-width are fixed. Only the table changes;
-- its actual list length is at most D, and each entry has at most S+D bits. Thus this
-- envelope is derived from components, not a repeated polynomial output-size estimate.
private def rotationBudget (encRel : Rel ↪ List Bool) (I : State Rel) : ℕ :=
  let S := (encState encRel I).length
  let D := I.rotation.successor.length + 2 * (I.body.occurrences.length + I.ports.length)
  4 * S + 4 + D * (2 * (S + D) + 1)

private theorem loop_size (encRel : Rel ↪ List Bool) (b : Bool) (I : State Rel) (n : ℕ) :
    (encState encRel ((turn b)^[n] I)).length ≤ rotationBudget encRel I := by
  have h := loop_components encRel b I n
  have hp := enc_ports_perm h.2.1
  let S := (encState encRel I).length
  let D := I.rotation.successor.length + 2 * (I.body.occurrences.length + I.ports.length)
  have ht : (encList encNat ((turn b)^[n] I).rotation.successor).length ≤
      D * (2 * (S + D) + 1) := by
    have hwidth : ∀ v ∈ ((turn b)^[n] I).rotation.successor,
        (encNat v).length ≤ S + D := by
      intro v hv
      rw [encNat_apply, Nat.size_eq_bits_len]
      exact (h.2.2.2 v hv).trans (by dsimp only [S, D]; omega)
    exact (length_encList_le encNat _ hwidth).trans
      (Nat.mul_le_mul_right _ (h.2.2.1.trans (max_le (by omega) (by omega))))
  have hbp : (encCSP encRel encNat I.body).length ≤ S ∧
      (encList encNat I.ports).length ≤ S := by
    constructor <;> dsimp only [S] <;>
      enc_len [encState_apply, encStateFields, Graph.encRotationCertificate_apply,
        Graph.encRotationCertificateFields]
  change (encState encRel ((turn b)^[n] I)).length ≤
    4 * S + 4 + D * (2 * (S + D) + 1)
  simp only [encState_apply, encStateFields, Graph.encRotationCertificate_apply,
    Graph.encRotationCertificateFields, length_encPair]
  rw [h.1, hp]
  omega

private theorem rotationBudget_poly (encRel : Rel ↪ List Bool) :
    PolyBounded (fun I : State Rel => (encState encRel I).length)
      (rotationBudget encRel) := by
  have hbody := encState_body_polyTime encRel (ComputableInPolyTime.id' (encIn := encState encRel))
  have hm : ComputableInPolyTime (fun I : State Rel => I.body.occurrences.length)
      (encState encRel) encUnary := by
    simpa only [CSP.vars_length_eq_occurrences, Function.comp_def] using
      (computableInPolyTime_length_vars encRel encNat).comp hbody
  growth_poly

private def boundedTurn (b : Bool) (I : State Rel) (n : ℕ) : State Rel :=
  (turn b)^[min I.ports.length n] I

private theorem boundedTurn_poly (encRel : Rel ↪ List Bool) (b : Bool) :
    ComputableInPolyTime (fun p : State Rel × ℕ => boundedTurn b p.1 p.2)
      (encPair (encState encRel) encNat) (encState encRel) := by
  have hI := ComputableInPolyTime.fst (encState encRel) encNat
  have hn := ComputableInPolyTime.snd (encState encRel) encNat
  have hP := (ComputableInPolyTime.length_list encNat).comp
    (encState_ports_polyTime encRel hI)
  have hc := ComputableInPolyTime.binary_min_unary' hP hn
  have hs : ComputableInPolyTime (turn b (Rel := Rel)) (encState encRel) (encState encRel) := by
    cases b
    exacts [computableInPolyTime_rotateLeft encRel, computableInPolyTime_rotateRight encRel]
  have hbound := (rotationBudget_poly encRel).comp hI.polyBounded_length
  exact (ComputableInPolyTime.iterate_spec hc hI hs
    (fun p i J => J = (turn b)^[i] p.1)
    (fun _ => rfl)
    (fun p i J _ hJ => by rw [hJ, Function.iterate_succ_apply'])
    hbound (fun p i J _ hJ => by rw [hJ]; exact loop_size encRel b p.1 i)).1

private theorem tail_ports_length (I : State Rel) :
    (transposeTail g w I).ports.length = I.ports.length := by
  rcases I with ⟨F, ports, c⟩
  induction ports using List.reverseRecOn with
  | nil => rfl
  | append_singleton ps y _ =>
    cases ps using List.reverseRecOn with
    | nil => rfl
    | append_singleton L x => simp [List.append_assoc, length_transposeTail_ports]

/-- Plain polynomial time on EVERY raw state and binary position for any encoded alphabet.
The position is capped by actual unary port length before either loop. Reachable rotation
states have an internal component/bit-width budget; no growth provider is a hypothesis. -/
theorem computableInPolyTime_transposeAdjacent (encRel : Rel ↪ List Bool) :
    ComputableInPolyTime (fun p : State Rel × ℕ => transposeAdjacent g w p.1 p.2)
      (encPair (encState encRel) encNat) (encState encRel) := by
  have hI := ComputableInPolyTime.fst (encState encRel) encNat
  have hj := ComputableInPolyTime.snd (encState encRel) encNat
  have hP := (ComputableInPolyTime.length_list encNat).comp
    (encState_ports_polyTime encRel hI)
  have hj2 := ComputableInPolyTime.binary_add' hj (ComputableInPolyTime.const 2)
  have hcap := ComputableInPolyTime.binary_min_unary' hP hj2
  have hr := ComputableInPolyTime.unary_sub' hP hcap
  have hrbin := ComputableInPolyTime.unary_to_binary.comp hr
  have hpre := (boundedTurn_poly encRel true).comp (hI.prod hrbin)
  have hmid := (computableInPolyTime_transposeTail g w encRel).comp hpre
  have hpost := (boundedTurn_poly encRel false).comp (hmid.prod hrbin)
  have hguard := ComputableInPolyTime.binary_lt'
    (ComputableInPolyTime.binary_add' hj (ComputableInPolyTime.const 1))
    (ComputableInPolyTime.unary_to_binary.comp hP)
  refine (ComputableInPolyTime.ite_decide hguard hpost hI).of_enc_eq fun ⟨I, j⟩ =>
    congrArg (encState encRel) ?_
  have hr : I.ports.length - min I.ports.length (j + 2) = I.ports.length - (j + 2) := by omega
  have hle : I.ports.length - (j + 2) ≤ I.ports.length := Nat.sub_le _ _
  have hp := (loop_components encRel true I (I.ports.length - (j + 2))).2.1.length_eq
  simp only [transposeAdjacent, boundedTurn, hr, Nat.min_eq_right hle, Function.comp_def]
  split_ifs
  · rw [tail_ports_length, hp, Nat.min_eq_right hle]
    rfl
  · rfl

private theorem normalized_turn_length (b : Bool) (I : State Rel)
    (hl : I.rotation.successor.length = 2 * (I.body.occurrences.length + I.ports.length)) :
    (turn b I).rotation.successor.length =
      2 * ((turn b I).body.occurrences.length + (turn b I).ports.length) := by
  rcases I with ⟨F, ps, c⟩
  cases ps with
  | nil => simpa [turn, rotateLeft, rotateRight] using hl
  | cons x ps =>
    cases ps <;> cases b <;>
      simp_all [turn, rotateLeft, rotateRight, rotateBoundaryCertificate,
        rotateBoundaryCertificateRight_eq_reindex_mod, RotationCertificate.length_reindex]

private theorem normalized_loop_storage (b : Bool) (I : State Rel) (n B : ℕ)
    (hl : I.rotation.successor.length = 2 * (I.body.occurrences.length + I.ports.length))
    (he : ∀ v ∈ I.rotation.successor, v.size ≤ B)
    (hb : (2 * (I.body.occurrences.length + I.ports.length)).size ≤ B) :
    ((turn b)^[n] I).body = I.body ∧ ((turn b)^[n] I).ports.length = I.ports.length ∧
    ((turn b)^[n] I).rotation.successor.length =
      2 * (I.body.occurrences.length + I.ports.length) ∧
    ∀ v ∈ ((turn b)^[n] I).rotation.successor, v.size ≤ B := by
  induction n with
  | zero => exact ⟨rfl, rfl, hl, he⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    obtain ⟨hbody, hplen, hslen, hsize⟩ := ih
    have ht := turn_table b ((turn b)^[n] I) B hsize (by simpa only [hbody, hplen] using hb)
    refine ⟨(turn_body _ _).trans hbody, (turn_ports_perm _ _).length_eq.trans hplen, ?_, ht.2⟩
    simpa only [turn_body, (turn_ports_perm b ((turn b)^[n] I)).length_eq, hbody, hplen] using
      normalized_turn_length b ((turn b)^[n] I) (by simpa only [hbody, hplen] using hslen)

/-- A valid raw step emits the actual dart count, with entry widths reset by its final
restriction. Arbitrary malformed source entries require no input bound or acceptance. -/
theorem storage_transposeAdjacent (I : State Rel) (j : ℕ) (h : j + 1 < I.ports.length) :
    (transposeAdjacent g w I j).rotation.successor.length =
        2 * (I.body.occurrences.length + g.body.occurrences.length + I.ports.length) ∧
      ∀ v ∈ (transposeAdjacent g w I j).rotation.successor,
        v.size ≤ (2 * (I.body.occurrences.length + g.body.occurrences.length +
          I.ports.length + 4)).size := by
  let r := I.ports.length - (j+2)
  let J := (rotateRight^[r]) I
  let H := transposeTail g w J
  have hpJ : J.ports.length = I.ports.length := by
    rw [right_ports, List.length_reverse, List.length_rotate, List.length_reverse]
  have hpH : H.ports.length = I.ports.length := by rw [tail_ports_length, hpJ]
  have hout : transposeAdjacent g w I j = (rotateLeft^[r]) H := by
    rw [transposeAdjacent, ite_eq_left h]
  have hmH : H.body.occurrences.length =
      I.body.occurrences.length + g.body.occurrences.length := by
    have hc := (counts_transposeAdjacent g w I j).2.1
    rwa [hout, left_body, ite_eq_left h, one_mul] at hc
  have ht := storage_transposeTail g w J (by rw [hpJ]; omega)
  let B := (2 * (I.body.occurrences.length + g.body.occurrences.length +
    I.ports.length + 4)).size
  have hb : (2 * (H.body.occurrences.length + H.ports.length)).size ≤ B := by
    simpa only [hmH, hpH] using (Nat.size_le_size (Nat.mul_le_mul_left 2
      (Nat.le_add_right
        (I.body.occurrences.length + g.body.occurrences.length + I.ports.length) 4)))
  obtain ⟨-, -, hslen, hsize⟩ := normalized_loop_storage false H r B
    (by simpa only [hpJ, hpH] using ht.1)
    (by simpa only [J, right_body, hpJ] using ht.2) hb
  change ((rotateLeft^[r]) H).rotation.successor.length = _ at hslen
  exact hout ▸ ⟨by simpa only [hmH, hpH] using hslen, hsize⟩

end Cslib.Complexity.CSP.CrossInsertion
