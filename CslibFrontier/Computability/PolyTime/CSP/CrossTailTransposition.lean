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
  · have h0 := accepted_insert g w I hI
    have h1 := accepted_rotateRight _ h0
    have h2 := accepted_rotateRight _ h1
    have h3 := accepted_rotateRight _ h2
    have h4 := accepted_rotateRight _ h3
    have h5 := accepted_rotateRight _ h4
    have h6 := accepted_hideHead _ (accepted_fuseHead _ h5)
    have h7 := accepted_rotateRight _ h6
    have h8 := accepted_hideHead _ (accepted_fuseHead _ h7)
    exact accepted_rotateLeft _ (accepted_rotateLeft _ h8)

/-- Fixed composition is plain polynomial time on EVERY raw State, for any encoded
relation alphabet. Actual lists fund the primitive clocks; binary labels/entries remain
data. The fixed template and witness are constants outside runtime, not runtime search. -/
theorem computableInPolyTime_transposeTail (encRel : Rel ↪ List Bool) :
    ComputableInPolyTime (transposeTail g w) (encState encRel) (encState encRel) := by
  let input := encState encRel
  have hr := computableInPolyTime_rotateRight encRel
  have hl := computableInPolyTime_rotateLeft encRel
  have hf := computableInPolyTime_fuseHead encRel
  have hh := computableInPolyTime_hideHead encRel
  have h0 := computableInPolyTime_insert g w encRel
  have h1 := hr.comp h0
  have h2 := hr.comp h1
  have h3 := hr.comp h2
  have h4 := hr.comp h3
  have h5 := hr.comp h4
  have h6 := hh.comp (hf.comp h5)
  have h7 := hr.comp h6
  have h8 := hh.comp (hf.comp h7)
  have hout := hl.comp (hl.comp h8)
  have hports := encState_ports_polyTime encRel (ComputableInPolyTime.id' (encIn := input))
  have hshort := ComputableInPolyTime.binary_lt'
    (ComputableInPolyTime.unary_to_binary.comp
      ((ComputableInPolyTime.length_list encNat).comp hports)) (ComputableInPolyTime.const 2)
  apply (ComputableInPolyTime.ite_decide hshort
    (ComputableInPolyTime.id' (encIn := input)) hout).of_enc_eq
  intro I
  rfl

private theorem right_fields (J : State Rel) (ps : List ℕ) (p : ℕ)
    (hp : J.ports = ps ++ [p]) :
    (rotateRight J).body = J.body ∧ (rotateRight J).ports = p :: ps := by
  rcases J with ⟨F, ports, c⟩
  change ports = ps ++ [p] at hp
  subst ports
  rw [rotateRight_snoc]
  exact ⟨rfl, rfl⟩

private theorem seam_fields (J : State Rel) (a b : ℕ) (ps : List ℕ)
    (hp : J.ports = a :: b :: ps) :
    (hideHead (fuseHead J)).body = J.body.relabel (Function.update id b a) ∧
      (hideHead (fuseHead J)).ports = ps.map (Function.update id b a) := by
  rcases J with ⟨F, ports, c⟩
  change ports = a :: b :: ps at hp
  subst ports
  constructor <;> rfl

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
  have he0 (z : ℕ) : u0 (2 * z) = 2 * z := by
    dsimp only [u0]
    rw [Function.update_of_ne (by omega)]
    rfl
  have hE0 : E.map u0 = E := by
    dsimp only [E]
    rw [List.map_map]
    apply List.map_congr_left
    intro z _
    exact he0 z
  have hp6 : J6.ports = [3, 5, 7] ++ E ++ [X] := by
    have hp := h6.2
    change J6.ports = ([3, 5, 7] ++ E ++ [X]).map u0 at hp
    rw [hp]
    simp only [List.map_append, List.map_cons, List.map_nil, hE0]
    simp [u0, X]
  have h7 := right_fields J6 ([3, 5, 7] ++ E) X
    (by simpa only [List.append_assoc] using hp6)
  have h8 := seam_fields J7 X 3 ([5, 7] ++ E)
    (by simpa only [J7, List.append_assoc, List.cons_append, List.nil_append] using h7.2)
  have he1 (z : ℕ) : u1 (2 * z) = 2 * z := by
    dsimp only [u1]
    rw [Function.update_of_ne (by omega)]
    rfl
  have hE1 : E.map u1 = E := by
    dsimp only [E]
    rw [List.map_map]
    apply List.map_congr_left
    intro z _
    exact he1 z
  have hp8 : J8.ports = [5, 7] ++ E := by
    have hp := h8.2
    change J8.ports = ([5, 7] ++ E).map u1 at hp
    rw [hp]
    simp only [List.map_append, List.map_cons, List.map_nil, hE1]
    rfl
  have hb8 : J8.body = (J0.body.relabel u0).relabel u1 := by
    rw [show J8.body = _ from h8.1, show J7.body = _ from h7.1,
      show J6.body = _ from h6.1, show J5.body = _ from h5.1,
      show J4.body = _ from h4.1, show J3.body = _ from h3.1,
      show J2.body = _ from h2.1, show J1.body = _ from h1.1]
  have hlong : ¬I.ports.length < 2 := by simp [I]
  change (transposeTail g w I).body = _ ∧ (transposeTail g w I).ports = _
  rw [transposeTail, ite_eq_right hlong]
  change (rotateLeft (rotateLeft J8)).body = _ ∧
    (rotateLeft (rotateLeft J8)).ports = _
  rw [rotateLeft_body, rotateLeft_body, hb8, rotateLeft_ports, rotateLeft_ports, hp8]
  constructor
  · rfl
  · simp [List.rotate_cons_succ, List.append_assoc, E]

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
  rw [(long_fields g w F L x y c).1, CSP.eval_relabel, CSP.eval_relabel]
  rfl


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
  have he (z : ℕ) : ρ (2 * z) = σ z := by
    simp [ρ, σ, u0, u1, Function.comp_def,
      show 2 * z ≠ 1 from by omega, show 2 * z ≠ 3 from by omega]
  have hsource := (eval_insert_iff g w I σ a).mpr ⟨ρ, hr, he, fun _ => rfl⟩
  have ha := hsource.2
  have h5 : τ 5 = τ (2 * y) := by
    have h := ha.1
    simpa [a, ρ, u0, u1, cross, Function.comp_def,
      show 2 * y ≠ 3 from by omega] using h.symm
  have h7 : τ 7 = τ (2 * x) := by
    have h := ha.2
    simpa [a, ρ, u0, u1, cross, Function.comp_def] using h.symm
  refine ⟨hsource.1, ?_⟩
  rw [ports_transposeTail, List.map_append, List.map_map]
  simp only [Function.comp_def, List.map_cons, List.map_nil, h5, h7]

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
      by_cases h0 : z = 1
      · subst z
        simpa [u0, u1, a, Function.comp_def, hy3] using
          (he y).trans (hf (0 : Fin 4)).symm
      · by_cases h1 : z = 3
        · subst z
          simpa [u0, u1, a, Function.comp_def, h0] using
            (he x).trans (hf (1 : Fin 4)).symm
        · simp [u0, u1, Function.comp_def, h0, h1]
    refine ⟨τ, ?_, he, ?_⟩
    · rw [eval_long, show τ ∘ Function.update id 3 (2 * x) ∘
        Function.update id 1 (2 * y) = τ from hsame]
      exact ht
    · rw [ports_transposeTail, List.map_append, List.map_map]
      have hL : (L.map (fun z => τ (2 * z))) = L.map σ := by
        exact congrArg (fun f : ℕ → Bool => L.map f) (funext he)
      simp only [Function.comp_def, List.map_cons, List.map_nil, hL,
        show τ 5 = σ y from by simpa [a] using hf (2 : Fin 4),
        show τ 7 = σ x from by simpa [a] using hf (3 : Fin 4)]
  · rintro ⟨τ, ht, he, _⟩
    have hσ : (fun z => τ (2 * z)) = σ := funext he
    simpa only [hσ] using (recover_transposeTail g w F L x y c τ ht).1

/-- Long-branch rows are exactly the old rows plus the fixed actual gadget rows. -/
theorem length_transposeTail_body (F : CSP Rel ℕ) (L : List ℕ) (x y : ℕ)
    (c : Graph.RotationCertificate) :
    (transposeTail g w (⟨F, L ++ [x, y], c⟩ : State Rel)).body.length =
      F.length + g.body.length := by
  rw [(long_fields g w F L x y c).1]
  simpa only [CSP.relabel, List.length_map] using
    length_insert_body g w (⟨F, L ++ [x, y], c⟩ : State Rel)

/-- Relabeling seams retains every occurrence, including repeated visits. -/
theorem length_transposeTail_occurrences (F : CSP Rel ℕ) (L : List ℕ) (x y : ℕ)
    (c : Graph.RotationCertificate) :
    (transposeTail g w (⟨F, L ++ [x, y], c⟩ : State Rel)).body.occurrences.length =
      F.occurrences.length + g.body.occurrences.length := by
  rw [(long_fields g w F L x y c).1]
  simpa only [CSP.occurrences_relabel, List.length_map] using
    length_insert_occurrences g w (⟨F, L ++ [x, y], c⟩ : State Rel)

/-- The two seam deletions restore the original number of boundary positions. -/
theorem length_transposeTail_ports (F : CSP Rel ℕ) (L : List ℕ) (x y : ℕ)
    (c : Graph.RotationCertificate) :
    (transposeTail g w (⟨F, L ++ [x, y], c⟩ : State Rel)).ports.length = L.length + 2 := by
  rw [ports_transposeTail]
  simp only [List.length_append, List.length_map, List.length_cons, List.length_nil]


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
      have htail : ps.length ≤ P := by
        change ps.length + 1 ≤ P at hp
        exact (Nat.le_succ _).trans hp
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
  dsimp only
  let I : State Rel := ⟨F, L ++ [x, y], c⟩
  let M := F.occurrences.length + g.body.occurrences.length
  let P := L.length + 2 + 4
  have h0 : (insert g w I).body.occurrences.length = M ∧
      (insert g w I).ports.length ≤ P ∧
      (insert g w I).rotation.successor.length ≤ 2 * (M + P) := by
    simp only [length_insert_occurrences, length_insert_ports, length_insert_rotation,
      I, List.length_append, List.length_cons, List.length_nil]
    dsimp only [M, P]
    omega
  have step (J : State Rel) (h : J.body.occurrences.length = M ∧ J.ports.length ≤ P ∧
      J.rotation.successor.length ≤ 2 * (M + P)) := primitive_bounds J M P h.1 h.2.1 h.2.2
  let J0 := insert g w I
  let J1 := rotateRight J0
  have h1 := step J0 h0 J1
    (by simp only [List.mem_cons]; exact Or.inl rfl)
  let J2 := rotateRight J1
  have h2 := step J1 h1 J2
    (by simp only [List.mem_cons]; exact Or.inl rfl)
  let J3 := rotateRight J2
  have h3 := step J2 h2 J3
    (by simp only [List.mem_cons]; exact Or.inl rfl)
  let J4 := rotateRight J3
  have h4 := step J3 h3 J4
    (by simp only [List.mem_cons]; exact Or.inl rfl)
  let J5 := rotateRight J4
  have h5 := step J4 h4 J5
    (by simp only [List.mem_cons]; exact Or.inl rfl)
  let J6 := fuseHead J5
  have h6 := step J5 h5 J6
    (by simp only [List.mem_cons]; exact Or.inr (Or.inr (Or.inl rfl)))
  let J7 := hideHead J6
  have h7 := step J6 h6 J7
    (by simp only [List.mem_cons]; exact Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  let J8 := rotateRight J7
  have h8 := step J7 h7 J8
    (by simp only [List.mem_cons]; exact Or.inl rfl)
  let J9 := fuseHead J8
  have h9 := step J8 h8 J9
    (by simp only [List.mem_cons]; exact Or.inr (Or.inr (Or.inl rfl)))
  let J10 := hideHead J9
  have h10 := step J9 h9 J10
    (by simp only [List.mem_cons]; exact Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  let J11 := rotateLeft J10
  have h11 := step J10 h10 J11
    (by simp only [List.mem_cons]; exact Or.inr (Or.inl rfl))
  let J12 := rotateLeft J11
  have h12 := step J11 h11 J12
    (by simp only [List.mem_cons]; exact Or.inr (Or.inl rfl))
  intro K hK
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hK
  rcases hK with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | exact h0.2.2 | exact h1.2.2 | exact h2.2.2 | exact h3.2.2 | exact h4.2.2 |
      exact h5.2.2 | exact h6.2.2 | exact h7.2.2 | exact h8.2.2 | exact h9.2.2 |
      exact h10.2.2 | exact h11.2.2 | exact h12.2.2

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
  have hupdate (z : ℕ) (hz : z.size ≤ B) : (u1 (u0 z)).size ≤ B := by
    by_cases h1 : z = 1
    · subst z; simpa [u0, u1, show 2 * y ≠ 3 from by omega] using hy
    · by_cases h3 : z = 3
      · subst z; simpa [u0, u1] using hx
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
  · rw [CSP.vars_relabel, CSP.vars_relabel] at hz
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hz
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
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


end Cslib.Complexity.CSP.CrossInsertion
