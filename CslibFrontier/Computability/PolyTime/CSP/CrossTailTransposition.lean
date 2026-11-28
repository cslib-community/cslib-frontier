/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.CSP.BoundaryRotation
public import CslibFrontier.Computability.PolyTime.CSP.BoundaryFusion
public import CslibFrontier.Computability.PolyTime.CSP.BoundaryHiding
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Mathlib.Data.List.Rotate

import Mathlib.Data.List.GetD

/-!
# A computed CROSS tail-value transposition

`CrossInsertion.transposeTail` inserts one fixed actual CROSS and joins its first two
ports to the old tail. The output positions use fresh names `5,7`, carrying the two old
values in opposite order. This is a value transposition, not a permutation of old names.

The program executes thirteen fixed primitive calls, including eight directed rotations.
No raw cycle is canceled: malformed reindexing can pad or discard entries. Inputs with
fewer than two ports retain their entire original state before insertion. The long branch
agrees with the original assignment on every doubled old name; the short branch has
ordinary identity semantics. Closed/nullary rows and repeated raw names remain explicit.

This original one-operation result is a step in
[#3091](https://github.com/cslib-community/cslib-frontier/issues/3091). Routing, variable
iteration, the full compiler, source criterion and hardness remain open there.

## Main definitions

* `CrossInsertion.transposeTail`: the literal fixed composition with a short-input guard.

## Main results

* `CrossInsertion.accepted_transposeTail`: internally derived full checker preservation.
* `CrossInsertion.eval_transposeTail_iff`: extension on every even old name.
* `CrossInsertion.recover_transposeTail`: recover source satisfaction and reversed `y,x` values.
* `CrossInsertion.computableInPolyTime_transposeTail`: plain time on every raw encoded state.
* `CrossInsertion.emitted_rotation_lengths_le`: a single-insertion bound on all thirteen tables.
* `CrossInsertion.name_width_transposeTail_le`: one old-name bit growth, separate from runtime.
-/

public section

namespace Cslib.Complexity.CSP.CrossInsertion

open Cslib.Logic.PL Cslib.Logic.PL.CSP Cslib.Logic.PL.CSP.Crossover
open OrderedBoundary Cslib.BitString Turing.MultiTapeTM

variable {Rel : Type} {ar : Rel → ℕ} {sem : Rel → List Bool → Bool}
variable (g : PPGadget ar sem cross) (w : GadgetWitness g)

/-- Insert once, move RIGHT five times, fuse/hide, move RIGHT once, fuse/hide, and move
LEFT twice. These are thirteen actual calls, not iteration modulo the boundary length.
Short inputs return the ENTIRE original state before any tagging or insertion. -/
@[expose] def transposeTail (I : State Rel) : State Rel :=
  if I.ports.length < 2 then I else
    let J := insert g w I
    let J := rotateRight (rotateRight (rotateRight (rotateRight (rotateRight J))))
    let J := hideHead (fuseHead J)
    let J := rotateRight J
    let J := hideHead (fuseHead J)
    rotateLeft (rotateLeft J)

/-- Empty and singleton raw boundaries retain all original rows, names and malformed data.
The guard is before insertion, so no doubled-name semantic condition is imposed here. -/
theorem transposeTail_short (I : State Rel) (h : I.ports.length < 2) :
    transposeTail g w I = I := by
  rw [transposeTail, ite_eq_left h]

/-- Every executed primitive supplies its own full checker theorem from the preceding
accepted state. No target certificate, rotation, order, genus or recognizer is supplied. -/
theorem accepted_transposeTail (I : State Rel) (hI : I.Accepted) :
    (transposeTail g w I).Accepted := by
  unfold transposeTail
  split_ifs with h
  · exact hI
  · exact accepted_rotateLeft _ (accepted_rotateLeft _
      (accepted_hideHead _ (accepted_fuseHead _
        (accepted_rotateRight _ (accepted_hideHead _ (accepted_fuseHead _
          (accepted_rotateRight _ (accepted_rotateRight _ (accepted_rotateRight _
            (accepted_rotateRight _ (accepted_rotateRight _
              (accepted_insert g w I hI))))))))))))

attribute [local fun_prop] computableInPolyTime_insert computableInPolyTime_rotateRight
  computableInPolyTime_rotateLeft computableInPolyTime_fuseHead computableInPolyTime_hideHead

/-- Fixed composition is plain polynomial time on EVERY raw State, for any encoded
relation alphabet. Actual lists fund the primitive clocks; binary labels/entries remain
data. The fixed template and witness are constants outside runtime, not runtime search. -/
theorem computableInPolyTime_transposeTail (encRel : Rel ↪ List Bool) :
    ComputableInPolyTime (transposeTail g w) (encState encRel) (encState encRel) := by
  open scoped State in
  unfold transposeTail
  dsimp only
  exact ComputableInPolyTime.ite_decide (by fun_prop) (by fun_prop) (by fun_prop)

private theorem right_fields (J : State Rel) (ps : List ℕ) (p : ℕ)
    (hp : J.ports = ps ++ [p]) :
    (rotateRight J).body = J.body ∧ (rotateRight J).ports = p :: ps := by
  rcases J with ⟨F, _, c⟩
  obtain rfl : _ = ps ++ [p] := hp
  simp [rotateRight_snoc]

private theorem seam_fields (J : State Rel) (a b : ℕ) (ps : List ℕ)
    (hp : J.ports = a :: b :: ps) :
    (hideHead (fuseHead J)).body = J.body.relabel (Function.update id b a) ∧
      (hideHead (fuseHead J)).ports = ps.map (Function.update id b a) := by
  rcases J with ⟨F, _, c⟩
  obtain rfl : _ = a :: b :: ps := hp
  exact ⟨rfl, rfl⟩

private theorem long_fields (F : CSP Rel ℕ) (L : List ℕ) (x y : ℕ)
    (c : Graph.RotationCertificate) :
    let I : State Rel := ⟨F, L ++ [x, y], c⟩
    (transposeTail g w I).body = ((insert g w I).body.relabel
      (Function.update id 1 (2 * y))).relabel (Function.update id 3 (2 * x)) ∧
    (transposeTail g w I).ports = L.map (2 * ·) ++ [5, 7] := by
  let I : State Rel := ⟨F, L ++ [x, y], c⟩
  let E := L.map (2 * ·)
  let X := 2 * x
  let Y := 2 * y
  let u0 := Function.update id 1 Y
  let u1 := Function.update id 3 X
  let J0 := insert g w I
  let J1 := rotateRight J0
  let J2 := rotateRight J1
  let J3 := rotateRight J2
  let J4 := rotateRight J3
  let J5 := rotateRight J4
  let J6 := hideHead (fuseHead J5)
  let J7 := rotateRight J6
  let J8 := hideHead (fuseHead J7)
  have hp0 : J0.ports = E ++ [X, Y, 1, 3, 5, 7] := by
    simp [J0, I, E, X, Y, insert, List.map_append, List.ofFn_succ]
  have h1 := right_fields J0 (E ++ [X, Y, 1, 3, 5]) 7
    (by simpa only [List.append_assoc, List.cons_append, List.nil_append] using hp0)
  have h2 := right_fields J1 ([7] ++ E ++ [X, Y, 1, 3]) 5
    (by simpa only [J1, List.append_assoc, List.cons_append, List.nil_append] using h1.2)
  have h3 := right_fields J2 ([5, 7] ++ E ++ [X, Y, 1]) 3
    (by simpa only [J2, List.append_assoc, List.cons_append, List.nil_append] using h2.2)
  have h4 := right_fields J3 ([3, 5, 7] ++ E ++ [X, Y]) 1
    (by simpa only [J3, List.append_assoc, List.cons_append, List.nil_append] using h3.2)
  have h5 := right_fields J4 ([1, 3, 5, 7] ++ E ++ [X]) Y
    (by simpa only [J4, List.append_assoc, List.cons_append, List.nil_append] using h4.2)
  have h6 := seam_fields J5 Y 1 ([3, 5, 7] ++ E ++ [X])
    (by simpa only [J5, List.append_assoc, List.cons_append, List.nil_append] using h5.2)
  have hE {a : ℕ} (b : ℕ) (ha : a % 2 = 1) : E.map (Function.update id a b) = E := by
    rw [List.map_map]
    exact List.map_congr_left fun z _ => by simpa using Function.update_of_ne (by omega) b id
  have hE0 : E.map u0 = E := hE Y rfl
  have hp6 : J6.ports = [3, 5, 7] ++ E ++ [X] := by simp [J6, h6.2, u0, X, hE0]
  have h7 := right_fields J6 ([3, 5, 7] ++ E) X
    (by simpa only [List.append_assoc] using hp6)
  have h8 := seam_fields J7 X 3 ([5, 7] ++ E)
    (by simpa only [J7, List.append_assoc, List.cons_append, List.nil_append] using h7.2)
  have hE1 : E.map u1 = E := hE X rfl
  have hp8 : J8.ports = [5, 7] ++ E := by simp [J8, h8.2, u1, hE1]
  have hb8 : J8.body = (J0.body.relabel u0).relabel u1 :=
    h8.1.trans (congrArg (·.relabel u1) (h7.1.trans (h6.1.trans (congrArg (·.relabel u0)
      (h5.1.trans (h4.1.trans (h3.1.trans (h2.1.trans h1.1))))))))
  have hlong : ¬I.ports.length < 2 := by simp [I]
  dsimp only
  rw [transposeTail, ite_eq_right hlong]
  dsimp only
  rw [rotateLeft_body, rotateLeft_body, hb8, rotateLeft_ports, rotateLeft_ports, hp8]
  exact ⟨rfl, by simp [List.rotate_cons_succ, List.append_assoc, E]⟩

/-- On a long raw boundary, the final ports have fresh tail names, not swapped old names.
Repeated or sparse old names and arbitrary malformed certificates require no hypothesis. -/
theorem ports_transposeTail (F : CSP Rel ℕ) (L : List ℕ) (x y : ℕ)
    (c : Graph.RotationCertificate) :
    (transposeTail g w (⟨F, L ++ [x, y], c⟩ : State Rel)).ports =
      L.map (2 * ·) ++ [5, 7] := (long_fields g w F L x y c).2

private theorem eval_long (F : CSP Rel ℕ) (L : List ℕ) (x y : ℕ)
    (c : Graph.RotationCertificate) (τ : ℕ → Bool) :
    (transposeTail g w (⟨F, L ++ [x, y], c⟩ : State Rel)).body.eval sem τ =
      (insert g w (⟨F, L ++ [x, y], c⟩ : State Rel)).body.eval sem
        (τ ∘ Function.update id 3 (2 * x) ∘ Function.update id 1 (2 * y)) := by
  rw [(long_fields g w F L x y c).1, CSP.eval_relabel, CSP.eval_relabel]; rfl


/-- Recover source satisfaction and reversed tail values from any satisfying output
assignment. The recovered source assignment reads EVERY doubled old name, including
unused names. No accepted-state, distinctness, arity or prescribed-word premise is needed,
including for repeated raw names and malformed certificates. -/
theorem recover_transposeTail (F : CSP Rel ℕ) (L : List ℕ) (x y : ℕ)
    (c : Graph.RotationCertificate) (τ : ℕ → Bool)
    (ht : (transposeTail g w (⟨F, L ++ [x, y], c⟩ : State Rel)).body.eval sem τ = true) :
    F.eval sem (fun z => τ (2 * z)) = true ∧
      (transposeTail g w (⟨F, L ++ [x, y], c⟩ : State Rel)).ports.map τ =
        L.map (fun z => τ (2 * z)) ++ [τ (2 * y), τ (2 * x)] := by
  let I : State Rel := ⟨F, L ++ [x, y], c⟩
  let u0 := Function.update id 1 (2 * y)
  let u1 := Function.update id 3 (2 * x)
  let ρ := τ ∘ u1 ∘ u0
  let σ := fun z => τ (2 * z)
  let a : Fin 4 → Bool := fun i => ρ (2 * i.val + 1)
  have hr : (insert g w I).body.eval sem ρ = true := by
    simpa only [ρ, u0, u1] using (eval_long g w F L x y c τ).symm.trans ht
  have hne1 (z : ℕ) : 2 * z ≠ 1 := by omega
  have hne3 (z : ℕ) : 2 * z ≠ 3 := by omega
  have he (z : ℕ) : ρ (2 * z) = σ z := by
    simp [ρ, σ, u0, u1, Function.comp_def, hne1 z, hne3 z]
  obtain ⟨hF, h5', h7'⟩ := (eval_insert_iff g w I σ a).mpr ⟨ρ, hr, he, fun _ => rfl⟩
  have h5 : τ 5 = τ (2 * y) := by
    simpa [a, ρ, u0, u1, cross, Function.comp_def, hne3 y] using h5'.symm
  have h7 : τ 7 = τ (2 * x) := by
    simpa [a, ρ, u0, u1, cross, Function.comp_def] using h7'.symm
  refine ⟨hF, ?_⟩
  simp only [ports_transposeTail, List.map_append, List.map_map, Function.comp_def,
    List.map_cons, List.map_nil, h5, h7]

/-- Exact long-branch assignment extension: the output uses fresh tail names carrying
`y,x`, while agreeing on EVERY doubled old name, including unused names. There is no
semantic checker, distinctness, arity, well-formedness or word-length assumption. -/
theorem eval_transposeTail_iff (F : CSP Rel ℕ) (L : List ℕ) (x y : ℕ)
    (c : Graph.RotationCertificate) (σ : ℕ → Bool) :
    F.eval sem σ = true ↔
      ∃ τ : ℕ → Bool,
        (transposeTail g w (⟨F, L ++ [x, y], c⟩ : State Rel)).body.eval sem τ = true ∧
        (∀ z, τ (2 * z) = σ z) ∧
        (transposeTail g w (⟨F, L ++ [x, y], c⟩ : State Rel)).ports.map τ =
          L.map σ ++ [σ y, σ x] := by
  let I : State Rel := ⟨F, L ++ [x, y], c⟩
  let u0 := Function.update id 1 (2 * y)
  let u1 := Function.update id 3 (2 * x)
  constructor
  · intro hσ
    have hy3 : 2 * y ≠ 3 := by omega
    let a : Fin 4 → Bool := ![σ y, σ x, σ y, σ x]
    have ha : a ∈ cross := by simp [a, cross]
    obtain ⟨τ, ht, he, hf⟩ := (eval_insert_iff g w I σ a).mp ⟨hσ, ha⟩
    have hsame : τ ∘ u1 ∘ u0 = τ := by
      funext z
      rcases eq_or_ne z 1 with rfl | h0
      · simpa [u0, u1, a, Function.comp_def, hy3] using (he y).trans (hf (0 : Fin 4)).symm
      · rcases eq_or_ne z 3 with rfl | h1
        · simpa [u0, u1, a, Function.comp_def, h0] using (he x).trans (hf (1 : Fin 4)).symm
        · simp [u0, u1, Function.comp_def, h0, h1]
    refine ⟨τ, (eval_long g w F L x y c τ).trans
      ((congrArg ((insert g w I).body.eval sem) hsame).trans ht), he, ?_⟩
    have h5 : τ 5 = σ y := by simpa [a] using hf (2 : Fin 4)
    have h7 : τ 7 = σ x := by simpa [a] using hf (3 : Fin 4)
    simp only [ports_transposeTail, List.map_append, List.map_map, Function.comp_def, he,
      List.map_cons, List.map_nil, h5, h7]
  · rintro ⟨τ, ht, he, _⟩
    simpa only [funext he] using (recover_transposeTail g w F L x y c τ ht).1

/-- Exact arity is preserved on every raw input. Old malformed scopes stay malformed;
the fixed actual gadget supplies all new arity obligations. -/
theorem wellFormed_transposeTail_iff (I : State Rel) :
    (transposeTail g w I).body.WellFormed ar ↔ I.body.WellFormed ar := by
  have hrel (F : CSP Rel ℕ) (f : ℕ → ℕ) :
      (F.relabel f).WellFormed ar ↔ F.WellFormed ar :=
    ⟨fun h c hc => by
      have h' := h (c.relabel f) (List.mem_map.mpr ⟨c, hc, rfl⟩)
      simpa only [Constraint.relabel, List.length_map] using h', fun h => h.relabel f⟩
  by_cases hs : I.ports.length < 2
  · rw [transposeTail_short g w I hs]
  · rcases I with ⟨F, ports, c⟩
    cases ports using List.reverseRecOn with
    | nil => simp at hs
    | append_singleton ps y =>
      cases ps using List.reverseRecOn with
      | nil => simp at hs
      | append_singleton L x =>
        simp only [List.append_assoc, List.cons_append, List.nil_append,
          (long_fields g w F L x y c).1, hrel, wellFormed_insert_iff]

/-- Long-branch rows are exactly the old rows plus the fixed actual gadget rows. -/
theorem length_transposeTail_body (F : CSP Rel ℕ) (L : List ℕ) (x y : ℕ)
    (c : Graph.RotationCertificate) :
    (transposeTail g w (⟨F, L ++ [x, y], c⟩ : State Rel)).body.length =
      F.length + g.body.length := by
  simpa only [(long_fields g w F L x y c).1, CSP.relabel, List.length_map] using
    length_insert_body g w (⟨F, L ++ [x, y], c⟩ : State Rel)

/-- Relabeling seams retains every occurrence, including repeated visits. -/
theorem length_transposeTail_occurrences (F : CSP Rel ℕ) (L : List ℕ) (x y : ℕ)
    (c : Graph.RotationCertificate) :
    (transposeTail g w (⟨F, L ++ [x, y], c⟩ : State Rel)).body.occurrences.length =
      F.occurrences.length + g.body.occurrences.length := by
  simpa only [(long_fields g w F L x y c).1, CSP.occurrences_relabel, List.length_map] using
    length_insert_occurrences g w (⟨F, L ++ [x, y], c⟩ : State Rel)

/-- The two seam deletions restore the original number of boundary positions. -/
theorem length_transposeTail_ports (F : CSP Rel ℕ) (L : List ℕ) (x y : ℕ)
    (c : Graph.RotationCertificate) :
    (transposeTail g w (⟨F, L ++ [x, y], c⟩ : State Rel)).ports.length = L.length + 2 := by
  simp only [ports_transposeTail, List.length_append, List.length_map, List.length_cons,
    List.length_nil]


private theorem primitive_bounds (J : State Rel) (M P : ℕ)
    (hm : J.body.occurrences.length = M) (hp : J.ports.length ≤ P)
    (hc : J.rotation.successor.length ≤ 2 * (M + P)) :
    ∀ K ∈ [rotateRight J, rotateLeft J, fuseHead J, hideHead J],
      K.body.occurrences.length = M ∧ K.ports.length ≤ P ∧
        K.rotation.successor.length ≤ 2 * (M + P) := by
  rcases J with ⟨F, ports, c⟩
  intro K hK
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hK
  rcases hK with rfl | rfl | rfl | rfl <;>
    cases ports with
    | nil => exact ⟨hm, hp, hc⟩
    | cons a ps =>
      have htail : ps.length ≤ P := Nat.le_of_succ_le hp
      cases ps <;>
        simp_all [rotateRight, rotateLeft, fuseHead, hideHead, rotateBoundaryCertificate,
          rotateBoundaryCertificateRight, equalDropCertificate, length_restrictPrefix,
          Graph.RotationCertificate.length_reindex, CSP.occurrences_relabel,
          List.length_map, List.length_reverse]

/-- Every table EMITTED by the long branch has the single-insertion dart bound.
The original raw table length is separate input data; it is not bounded by this theorem.
The displayed list is the actual thirteen-call trace, not an alternate compiler. -/
theorem emitted_rotation_lengths_le (F : CSP Rel ℕ) (L : List ℕ) (x y : ℕ)
    (c : Graph.RotationCertificate) :
    let I : State Rel := ⟨F, L ++ [x, y], c⟩
    let J0 := insert g w I
    let J1 := rotateRight J0
    let J2 := rotateRight J1
    let J3 := rotateRight J2
    let J4 := rotateRight J3
    let J5 := rotateRight J4
    let J6 := fuseHead J5
    let J7 := hideHead J6
    let J8 := rotateRight J7
    let J9 := fuseHead J8
    let J10 := hideHead J9
    let J11 := rotateLeft J10
    let J12 := rotateLeft J11
    ∀ K ∈ [J0, J1, J2, J3, J4, J5, J6, J7, J8, J9, J10, J11, J12],
      K.rotation.successor.length ≤
        2 * (F.occurrences.length + g.body.occurrences.length + (L.length + 2) + 4) := by
  intro I J0 J1 J2 J3 J4 J5 J6 J7 J8 J9 J10 J11 J12
  let M := F.occurrences.length + g.body.occurrences.length
  let P := L.length + 2 + 4
  let Inv (J : State Rel) : Prop :=
    J.body.occurrences.length = M ∧ J.ports.length ≤ P ∧
      J.rotation.successor.length ≤ 2 * (M + P)
  have h0 : Inv J0 := by
    simp only [Inv, J0, length_insert_occurrences, length_insert_ports, length_insert_rotation,
      I, List.length_append, List.length_cons, List.length_nil]
    exact ⟨rfl, le_rfl, by dsimp only [M, P]; omega⟩
  have cons {J J' : State Rel} {Js : List (State Rel)}
      (hJ' : J' ∈ [rotateRight J, rotateLeft J, fuseHead J, hideHead J])
      (hk : Inv J' → ∀ K ∈ J' :: Js, K.rotation.successor.length ≤ 2 * (M + P))
      (hJ : Inv J) : ∀ K ∈ J :: J' :: Js, K.rotation.successor.length ≤ 2 * (M + P) :=
    fun K hK => (List.mem_cons.mp hK).elim (fun h => h ▸ hJ.2.2)
      (hk (primitive_bounds J M P hJ.1 hJ.2.1 hJ.2.2 J' hJ') K)
  revert h0
  repeat apply cons (by simp +zetaDelta)
  intro h _ hK
  simpa using List.mem_singleton.mp hK ▸ h.2.2

/-- A safe single-insertion label-width bound. Fusion only selects an existing old label;
rotation/hiding introduce no names. This width lemma is not a premise of native runtime. -/
theorem name_width_transposeTail_le (F : CSP Rel ℕ) (L : List ℕ) (x y : ℕ)
    (c : Graph.RotationCertificate) (W : ℕ)
    (hW : ∀ z ∈ F.vars ++ (L ++ [x, y]), z.size ≤ W) :
    ∀ z ∈ (transposeTail g w (⟨F, L ++ [x, y], c⟩ : State Rel)).body.vars ++
      (transposeTail g w (⟨F, L ++ [x, y], c⟩ : State Rel)).ports,
      z.size ≤ max (W + 1) (2 * g.numAux + 7).size := by
  let I : State Rel := ⟨F, L ++ [x, y], c⟩
  let u0 := Function.update id 1 (2 * y)
  let u1 := Function.update id 3 (2 * x)
  let B := max (W + 1) (2 * g.numAux + 7).size
  have heven (z : ℕ) (hz : z.size ≤ W) : (2 * z).size ≤ B := by
    have h : (2 * z).size ≤ z.size + 1 := by
      by_cases h0 : z = 0
      · subst z; simp
      · simpa only [encNat_apply, Nat.size_eq_bits_len] using (length_evenName z h0).le
    exact (h.trans (Nat.add_le_add_right hz 1)).trans (le_max_left _ _)
  have hx := heven x (hW x (by simp))
  have hy := heven y (hW y (by simp))
  have hy3 : 2 * y ≠ 3 := by omega
  have hupdate (z : ℕ) (hz : z.size ≤ B) : (u1 (u0 z)).size ≤ B := by
    rcases eq_or_ne z 1 with rfl | h1
    · simpa [u0, u1, hy3] using hy
    · rcases eq_or_ne z 3 with rfl | h3
      · simpa [u0, u1] using hx
      · simpa [u0, u1, h1, h3] using hz
  have hvars : (insert g w I).body.vars = F.vars.map (2 * ·) ++
      g.body.vars.map (fun v => 2 * (finSumFinEquiv v).val + 1) := by
    calc
      _ = (F.relabel (2 * ·)).vars ++
          (g.body.relabel (fun v => 2 * (finSumFinEquiv v).val + 1)).vars := by
            simp only [I, insert, CSP.vars, List.flatMap_append]
      _ = _ := by rw [CSP.vars_relabel, CSP.vars_relabel]
  intro z hz
  rw [(long_fields g w F L x y c).1, ports_transposeTail] at hz
  rcases List.mem_append.mp hz with hz | hz
  · rw [CSP.vars_relabel, CSP.vars_relabel, List.map_map] at hz
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hz
    apply hupdate
    rw [hvars] at hb
    rcases List.mem_append.mp hb with hb | hb
    · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hb
      exact heven v (hW v (List.mem_append_left _ hv))
    · obtain ⟨v, _, rfl⟩ := List.mem_map.mp hb
      have hv := (finSumFinEquiv v).isLt
      exact (Nat.size_le_size (by omega : 2 * (finSumFinEquiv v).val + 1 ≤
        2 * g.numAux + 7)).trans (le_max_right _ _)
  · rcases List.mem_append.mp hz with hz | hz
    · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hz
      exact heven v (hW v (by simp [hv]))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl <;>
        exact (Nat.size_le_size (by omega)).trans (le_max_right _ _)


/-- The original row-symbol word is retained, followed by one fixed template word only
when insertion actually executes. No finite target alphabet or arity query is used. -/
theorem relations_transposeTail (I : State Rel) :
    (transposeTail g w I).body.map Constraint.rel = I.body.map Constraint.rel ++
      (if I.ports.length < 2 then [] else g.body.map Constraint.rel) := by
  by_cases hs : I.ports.length < 2
  · rw [transposeTail_short g w I hs, ite_eq_left hs, List.append_nil]
  · rcases I with ⟨F, ps, c⟩
    cases ps using List.reverseRecOn with
    | nil => simp at hs
    | append_singleton ps y =>
      cases ps using List.reverseRecOn with
      | nil => simp at hs
      | append_singleton L x =>
        simp [List.append_assoc, (long_fields g w F L x y c).1, insert, CSP.relabel,
          Constraint.relabel, List.map_map, Function.comp_def]

private theorem left_storage (J : State Rel) (B : ℕ)
    (hl : J.rotation.successor.length = 2 * (J.body.occurrences.length + J.ports.length))
    (he : ∀ v ∈ J.rotation.successor, v.size ≤ B)
    (hb : (2 * (J.body.occurrences.length + J.ports.length)).size ≤ B) :
    (rotateLeft J).rotation.successor.length =
        2 * ((rotateLeft J).body.occurrences.length + (rotateLeft J).ports.length) ∧
      ∀ v ∈ (rotateLeft J).rotation.successor, v.size ≤ B := by
  rcases J with ⟨F, ps, c⟩
  match ps with
  | [] | [_] => exact ⟨hl, he⟩
  | x :: y :: ps =>
    have hn : 0 < (x :: y :: ps).length := by simp
    refine ⟨by simp [rotateLeft, rotateBoundaryCertificate,
      Graph.RotationCertificate.length_reindex], fun v hv => ?_⟩
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hv
    have hr (j : ℕ) : (c.successor.getD j 0).size ≤ B := by
      by_cases hi : j < c.successor.length
      · exact List.getD_eq_getElem _ _ hi ▸ he _ (List.getElem_mem hi)
      · simp [hi]
    exact (size_boundaryIndexMap_le _ _ _
      (fun _ => Nat.mod_lt _ hn) _).trans (max_le (hr _) hb)

/-- Every long raw tail output has exactly its actual dart count and bounded entry widths.
The last executed hiding restriction supplies this bound even for malformed source data. -/
theorem storage_transposeTail (I : State Rel) (h : 2 ≤ I.ports.length) :
    (transposeTail g w I).rotation.successor.length =
        2 * ((transposeTail g w I).body.occurrences.length + I.ports.length) ∧
      ∀ v ∈ (transposeTail g w I).rotation.successor,
        v.size ≤ (2 * (I.body.occurrences.length + g.body.occurrences.length +
          I.ports.length + 4)).size := by
  let H := fuseHead (rotateRight (hideHead (fuseHead
    (rotateRight (rotateRight (rotateRight (rotateRight (rotateRight (insert g w I)))))))))
  let J := hideHead H
  have hout : transposeTail g w I = rotateLeft (rotateLeft J) := by
    rw [transposeTail, ite_eq_right (by omega)]
  have ⟨hports, hocc⟩ : (transposeTail g w I).ports.length = I.ports.length ∧
      (transposeTail g w I).body.occurrences.length =
        I.body.occurrences.length + g.body.occurrences.length := by
    rcases I with ⟨F, ps, c⟩
    cases ps using List.reverseRecOn with
    | nil => simp at h
    | append_singleton ps y =>
      cases ps using List.reverseRecOn with
      | nil => simp at h
      | append_singleton L x =>
        simpa [List.append_assoc] using ⟨length_transposeTail_ports g w F L x y c,
          length_transposeTail_occurrences g w F L x y c⟩
  have hpJ : J.ports.length = I.ports.length := by
    rwa [hout, rotateLeft_ports, List.length_rotate, rotateLeft_ports, List.length_rotate] at hports
  have hmJ : J.body.occurrences.length =
      I.body.occurrences.length + g.body.occurrences.length := by
    rwa [hout, rotateLeft_body, rotateLeft_body] at hocc
  let B := (2 * (I.body.occurrences.length + g.body.occurrences.length +
    I.ports.length + 4)).size
  have hB : (2 * (J.body.occurrences.length + J.ports.length)).size ≤ B := by
    rw [hmJ, hpJ]
    exact Nat.size_le_size (by omega)
  have hj : J.rotation.successor.length = 2 * (J.body.occurrences.length + J.ports.length) ∧
      ∀ v ∈ J.rotation.successor, v.size ≤ B := by
    rcases H with ⟨F, ps, c⟩
    cases ps with
    | nil => change 0 = I.ports.length at hpJ; omega
    | cons x ps =>
      exact ⟨length_restrictPrefix _ _, fun v hv =>
        (Nat.size_le_size (entries_restrictPrefix_lt _ _ v hv).le).trans hB⟩
  have h1 := left_storage J B hj.1 hj.2 hB
  have hB1 : (2 * ((rotateLeft J).body.occurrences.length +
      (rotateLeft J).ports.length)).size ≤ B := by
    simpa only [rotateLeft_body, rotateLeft_ports, List.length_rotate] using hB
  have h2 := left_storage (rotateLeft J) B h1.1 h1.2 hB1
  rw [hout]
  exact ⟨by simpa only [rotateLeft_ports, List.length_rotate, hpJ] using h2.1, h2.2⟩

end Cslib.Complexity.CSP.CrossInsertion
