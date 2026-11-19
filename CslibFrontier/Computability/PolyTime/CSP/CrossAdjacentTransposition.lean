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
  rw [transposeAdjacent, ite_eq_right (by omega)]

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
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact accepted_rotateLeft _ ih

private theorem right_accepted (I : State Rel) (n : ℕ) (h : I.Accepted) :
    ((rotateRight^[n]) I).Accepted := by
  induction n with
  | zero => exact h
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact accepted_rotateRight _ ih

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
  dsimp only
  let I : State Rel := ⟨F, L ++ [x, y] ++ R, c⟩
  let J := (rotateRight^[R.length]) I
  have hstate := positioned_state F L x y R c
  have hb : J.body = F := congrArg (fun K : State Rel => K.body) hstate
  have hJ : J.ports = (R ++ L) ++ [x, y] :=
    congrArg (fun K : State Rel => K.ports) hstate
  have hvalid : L.length + 1 < I.ports.length := by
    simp only [I, List.length_append, List.length_cons, List.length_nil]
    omega
  have hr : I.ports.length - (L.length + 2) = R.length := by
    simp only [I, List.length_append, List.length_cons, List.length_nil]
    omega
  have hp := ports_transposeTail g w F (R ++ L) x y J.rotation
  rw [← hstate] at hp
  rw [transposeAdjacent, ite_eq_left hvalid, hr]
  refine ⟨left_body _ _, hb, hJ, ?_⟩
  rw [left_ports, hp, List.map_append]
  rw [show R.length = (R.map (2 * ·)).length from (List.length_map _).symm]
  rw [List.append_assoc, List.rotate_append_length_eq]

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
  have ht' : (transposeTail g w J).body.eval sem τ = true := by
    rw [← hf.1]
    exact ht
  dsimp only [J, I] at ht'
  rw [hj] at ht'
  have hrec := recover_transposeTail g w F (R ++ L) x y J.rotation τ ht'
  refine ⟨hrec.1, ?_⟩
  have hvalid : L.length + 1 < I.ports.length := by
    simp only [I, List.length_append, List.length_cons, List.length_nil]
    omega
  have hr : I.ports.length - (L.length + 2) = R.length := by
    simp only [I, List.length_append, List.length_cons, List.length_nil]
    omega
  rw [transposeAdjacent, ite_eq_left hvalid, hr, left_ports, List.map_rotate, hj, hrec.2]
  rw [List.map_append, List.append_assoc,
    show R.length = (R.map (fun z => τ (2 * z))).length from (List.length_map _).symm,
    List.rotate_append_length_eq]

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
    obtain ⟨τ, ht, he, _⟩ :=
      (eval_transposeTail_iff g w F (R ++ L) x y J.rotation σ).mp hσ
    have hout : (transposeAdjacent g w I L.length).body.eval sem τ = true := by
      rw [hf.1, hj]
      exact ht
    refine ⟨τ, hout, he, ?_⟩
    have hrec := (recover_transposeAdjacent g w F L x y R c τ hout).2
    simpa only [show (fun z => τ (2 * z)) = σ from funext he, he] using hrec
  · rintro ⟨τ, ht, he, _⟩
    have hrec := (recover_transposeAdjacent g w F L x y R c τ ht).1
    simpa only [show (fun z => τ (2 * z)) = σ from funext he] using hrec

/-- Wrong-arity old constraints stay wrong-arity; the actual CROSS supplies the new scopes. -/
theorem wellFormed_transposeAdjacent_iff (I : State Rel) (j : ℕ) :
    (transposeAdjacent g w I j).body.WellFormed ar ↔ I.body.WellFormed ar := by
  unfold transposeAdjacent
  split_ifs
  · rw [left_body, wellFormed_transposeTail_iff, right_body]
  · rfl

/-- Rows, occurrences and port counts for a valid positioned operation. These are
one-operation bounds, not an accumulated routing/iteration certificate. -/
theorem counts_transposeAdjacent (F : CSP Rel ℕ) (L : List ℕ) (x y : ℕ)
    (R : List ℕ) (c : RotationCertificate) :
    let K := transposeAdjacent g w (⟨F, L ++ [x, y] ++ R, c⟩ : State Rel) L.length
    K.body.length = F.length + g.body.length ∧
    K.body.occurrences.length = F.occurrences.length + g.body.occurrences.length ∧
    K.ports.length = L.length + 2 + R.length := by
  let I : State Rel := ⟨F, L ++ [x, y] ++ R, c⟩
  let J := (rotateRight^[R.length]) I
  have hf := positioned_fields g w F L x y R c
  have hj := positioned_state F L x y R c
  constructor
  · rw [hf.1, hj, length_transposeTail_body]
  constructor
  · rw [hf.1, hj, length_transposeTail_occurrences]
  · rw [ports_transposeAdjacent]
    simp only [List.length_append, List.length_map, List.length_cons, List.length_nil]

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
  have hW' : ∀ z ∈ F.vars ++ ((R ++ L) ++ [x, y]), z.size ≤ W := by
    intro z hz
    apply hW z
    simpa only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      or_assoc, or_left_comm, or_comm] using hz
  have ht := name_width_transposeTail_le g w F (R ++ L) x y J.rotation W hW'
  intro z hz
  rw [hf.1, hj, ports_transposeAdjacent] at hz
  apply ht z
  rw [ports_transposeTail]
  simpa only [List.map_append, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, or_assoc, or_left_comm, or_comm] using hz

-- The two offset loops are implementation details, with actual State steps throughout.
private def turn (right : Bool) (I : State Rel) : State Rel :=
  if right then rotateRight I else rotateLeft I

private theorem turn_body (b : Bool) (I : State Rel) : (turn b I).body = I.body := by
  cases b <;> simp only [turn, Bool.false_eq_true, ↓reduceIte, rotateLeft_body,
    rotateRight_body]

private theorem turn_ports_perm (b : Bool) (I : State Rel) :
    (turn b I).ports.Perm I.ports := by
  cases b
  · rw [turn, ite_eq_right (by decide), rotateLeft_ports]
    exact List.rotate_perm _ _
  · rw [turn, ite_eq_left rfl, rotateRight_ports]
    exact (List.reverse_perm _).trans
      ((List.rotate_perm _ _).trans (List.reverse_perm _))

private theorem window_size (M N : ℕ) (shift : ℕ → ℕ) (h : ∀ j, shift j < N)
    (v : ℕ) : (boundaryIndexMap M N shift v).size ≤
      max v.size (2 * (M + N)).size := by
  unfold boundaryIndexMap
  split_ifs
  · have hs := h (v / 2 - M)
    have hb := Nat.mod_lt v (by decide : 0 < 2)
    exact (Nat.size_le_size (by omega)).trans (le_max_right _ _)
  · exact le_max_left _ _

private theorem turn_table (b : Bool) (I : State Rel) (B : ℕ)
    (he : ∀ v ∈ I.rotation.successor, v.size ≤ B)
    (hd : (2 * (I.body.occurrences.length + I.ports.length)).size ≤ B) :
    (turn b I).rotation.successor.length ≤
      max I.rotation.successor.length (2 * (I.body.occurrences.length + I.ports.length)) ∧
    ∀ v ∈ (turn b I).rotation.successor, v.size ≤ B := by
  rcases I with ⟨F, ports, c⟩
  cases ports with
  | nil =>
    simpa only [turn, rotateLeft, rotateRight, ite_self, List.length_nil, Nat.add_zero] using
      (show c.successor.length ≤ max c.successor.length (2 * F.occurrences.length) ∧
        ∀ v ∈ c.successor, v.size ≤ B from ⟨le_max_left _ _, he⟩)
  | cons x ps =>
    cases ps with
    | nil =>
      simp only [turn, rotateLeft, rotateRight, ite_self]
      exact ⟨le_max_left _ _, he⟩
    | cons y ps =>
      let N := (x :: y :: ps).length
      let M := F.occurrences.length
      have hN : 1 < N := by simp [N]
      have hread (i : ℕ) : (c.successor.getD i 0).size ≤ B := by
        by_cases hi : i < c.successor.length
        · rw [List.getD_eq_getElem _ _ hi]
          exact he _ (List.getElem_mem hi)
        · rw [List.getD_eq_default _ _ (by omega)]
          simp
      have hentry (shift : ℕ → ℕ) (hs : ∀ j, shift j < N) (i : ℕ) :
          (boundaryIndexMap M N shift (c.successor.getD i 0)).size ≤ B :=
        (window_size M N shift hs _).trans (max_le (hread i) hd)
      cases b <;>
        simp only [turn, Bool.false_eq_true, ↓reduceIte, rotateLeft, rotateRight,
          rotateBoundaryCertificate, rotateBoundaryCertificateRight_eq_reindex_mod,
          show ¬(x :: y :: ps).length ≤ 1 from by simp, ↓reduceIte]
      all_goals
        constructor
        · rw [RotationCertificate.length_reindex]
          exact le_max_right _ _
        · intro v hv
          obtain ⟨i, _, rfl⟩ := List.mem_map.mp hv
          apply hentry
          intro j
          exact Nat.mod_lt _ (by omega)

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
  have hbody : (encCSP encRel encNat I.body).length ≤ S := by
    dsimp only [S]
    enc_len [encState_apply, encStateFields, Graph.encRotationCertificate_apply,
      Graph.encRotationCertificateFields]
  have hports : (encList encNat I.ports).length ≤ S := by
    dsimp only [S]
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
  let input := encState encRel
  have hbody := encState_body_polyTime encRel (ComputableInPolyTime.id' (encIn := input))
  have hports := encState_ports_polyTime encRel (ComputableInPolyTime.id' (encIn := input))
  have hrot := encState_rotation_polyTime encRel (ComputableInPolyTime.id' (encIn := input))
  have hm : ComputableInPolyTime (fun I : State Rel => I.body.occurrences.length)
      input encUnary := by
    simpa only [CSP.vars_length_eq_occurrences, Function.comp_def] using
      (computableInPolyTime_length_vars encRel encNat).comp hbody
  have hp := (ComputableInPolyTime.length_list encNat).comp hports
  have hd := (ComputableInPolyTime.length_list encNat).comp
    (RotationCertificate.computableInPolyTime_successor.comp hrot)
  have hD := hd.polyBounded.add ((PolyBounded.const 2).mul (hm.polyBounded.add hp.polyBounded))
  have hS := (ComputableInPolyTime.id' (encIn := input)).polyBounded_length
  exact (((PolyBounded.const 4).mul hS).add (.const 4)).add
    (hD.mul (((PolyBounded.const 2).mul (hS.add hD)).add (.const 1)))

private def boundedTurn (b : Bool) (I : State Rel) (n : ℕ) : State Rel :=
  (turn b)^[min I.ports.length n] I

private theorem boundedTurn_poly (encRel : Rel ↪ List Bool) (b : Bool) :
    ComputableInPolyTime (fun p : State Rel × ℕ => boundedTurn b p.1 p.2)
      (encPair (encState encRel) encNat) (encState encRel) := by
  let input := encPair (encState encRel) encNat
  have hI := ComputableInPolyTime.fst (encState encRel) encNat
  have hn := ComputableInPolyTime.snd (encState encRel) encNat
  have hP := (ComputableInPolyTime.length_list encNat).comp
    (encState_ports_polyTime encRel hI)
  have hc := ComputableInPolyTime.binary_min_unary' hP hn
  have hs : ComputableInPolyTime (turn b (Rel := Rel)) (encState encRel) (encState encRel) := by
    cases b
    · exact computableInPolyTime_rotateLeft encRel
    · exact computableInPolyTime_rotateRight encRel
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
    | append_singleton L x =>
      rw [show (L ++ [x]) ++ [y] = L ++ [x, y] by
        simp only [List.append_assoc, List.cons_append, List.nil_append],
        length_transposeTail_ports]
      simp only [List.length_append, List.length_cons, List.length_nil]

/-- Plain polynomial time on EVERY raw state and binary position for any encoded alphabet.
The position is capped by actual unary port length before either loop. Reachable rotation
states have an internal component/bit-width budget; no growth provider is a hypothesis. -/
theorem computableInPolyTime_transposeAdjacent (encRel : Rel ↪ List Bool) :
    ComputableInPolyTime (fun p : State Rel × ℕ => transposeAdjacent g w p.1 p.2)
      (encPair (encState encRel) encNat) (encState encRel) := by
  let input := encPair (encState encRel) encNat
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
  apply (ComputableInPolyTime.ite_decide hguard hpost hI).of_enc_eq
  intro p
  apply congrArg (encState encRel)
  rcases p with ⟨I, j⟩
  have hr : I.ports.length - min I.ports.length (j + 2) = I.ports.length - (j + 2) := by omega
  have hle : I.ports.length - (j + 2) ≤ I.ports.length := Nat.sub_le _ _
  have hp := (loop_components encRel true I (I.ports.length - (j + 2))).2.1.length_eq
  simp only [transposeAdjacent, boundedTurn, hr, Nat.min_eq_right hle, Function.comp_def]
  split_ifs
  · rw [tail_ports_length, hp, Nat.min_eq_right hle]
    rfl
  · rfl

end Cslib.Complexity.CSP.CrossInsertion
