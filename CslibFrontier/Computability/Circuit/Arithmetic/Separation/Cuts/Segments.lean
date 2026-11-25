/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Cuts.Blocks
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Cuts.Units
public import Mathlib.Data.Fintype.Option
import CslibFrontier.Foundations.Data.List.Append
import CslibFrontier.Foundations.Data.List.SelfDelimiting
import CslibFrontier.Foundations.Data.Nat.BigOperators
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Option
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Segments between the parties of a run

In Lemma I.2 of [AnthropicVPVNP2026] (modules `Nc.Cut.Defs`, `Nc.Cut.Rows` and
`Nc.Cut.StartA`), a run of `K` blocks on tapes `S` with one input has `K + K` *parties* (the
nodes of the paper): the blocks, `Fin.castAdd K κ`, and `K` input parties, `Fin.natAdd K κ`,
which hold the parts `x κ` of the input. The input is treated as one more tape, `none`, that the
input parties write and the blocks read.

What the party `a` writes on the tape `s` and the party `b` reads is the *segment* `X s a b`.
The concatenation of a row `X s a` is what `a` writes on `s`, the concatenation of a column is
what `b` reads from `s`, and `X s` has staircase support (`List.StairRefinement.Stair`). By the
existence and uniqueness of a common refinement, the sum over what the blocks emit, in
`Cut.runVal_blocks`, is a sum over the segments with staircase support, of the product of the
weights of the parties (`Cut.sum_segments`).

All segments between two parties, those of each tape closed by a separator (the end mark of the
paper), are put into one bit string (`Cut.segmentString`), from which they can be recovered.

## Main definitions

* `Cut.joinSegments`, `Cut.segmentString`: the segments on all tapes as one word with
  separators, and as a bit string.
* `Cut.blockEmission`: what a block emits, given what it writes for and reads from the parties.
* `Cut.partyWeight`, `Cut.segmentWeight`: the weight of what a party writes and reads, and the
  product of the weights of the parties.
* `Cut.parts`: the parts of a word, of `ℓ` letters each.
* `Cut.segments`: the finite set of the segments of at most `T` letters each.

## Main results

* `Cut.joinSegments_injective`, `Cut.segmentString_injective`: the segments are determined by
  their word with separators, and by their bit string.
* `Cut.sum_unitCount_le`: the number of units of the bit strings of a party.
* `Cut.sum_length_le_of_partyWeight_ne_zero`: a party writes at most `T` letters.
* `Cut.cat_parts`: the parts of a word concatenate to the word.
* `Cut.sum_segments`: the sum over what the blocks emit as a sum over segments.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Lemma I.2 (Section I.3), which Proposition J.2 of Appendix J applies; modules `Nc.Cut.Defs`,
  `Nc.Cut.Rows`, `Nc.Cut.StartA`, `Nc.Cut.Facts`
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Cut

open Finset List.StairRefinement Tape

section Strings

variable {Γ σ : Type*} [Fintype σ] {c : ℕ}

/-- The segments `X s` on all tapes `s` as one word: every segment is followed by the separator
`none`. -/
@[expose] noncomputable def joinSegments (X : σ → List Γ) : List (Option Γ) :=
  (univ : Finset σ).toList.flatMap fun s => (X s).map some ++ [none]

/-- The segments on all tapes are determined by their word with separators. -/
theorem joinSegments_injective :
    Function.Injective (joinSegments : (σ → List Γ) → List (Option Γ)) := by
  intro X X' h
  have key : (univ : Finset σ).toList.map X = (univ : Finset σ).toList.map X' := by
    refine List.flatMap_inj_of_length_eq (c := fun w : List Γ => w.map some ++ [none])
      (fun w w' r r' hw => ?_) (by simp) (by simpa [joinSegments, List.flatMap_map] using h)
    have hw' : w.map some ++ none :: r = w'.map some ++ none :: r' := by simpa using hw
    simpa [List.map_inj_right (Option.some_injective _)] using
      (List.append_cons_inj_of_notMem_prefix (by simp) (by simp)).1 hw'
  exact funext fun s => List.map_inj_left.1 key s (mem_toList.2 (mem_univ s))

private theorem length_joinSegments (X : σ → List Γ) :
    (joinSegments X).length = ∑ s, (X s).length + Fintype.card σ := by
  simp [joinSegments, List.length_flatMap, sum_add_distrib]

/-- The bit string of the segments on all tapes, for a code `cb` of the letters and of the
separator. -/
@[expose] noncomputable def segmentString (cb : Option Γ → BitString c) (X : σ → List Γ) :
    List Bool :=
  bitsOf cb (joinSegments X)

/-- The segments on all tapes are determined by their bit string. -/
theorem segmentString_injective {cb : Option Γ → BitString c} (hcb : Function.Injective cb)
    (hc : 0 < c) : Function.Injective (segmentString (σ := σ) cb) :=
  (bitsOf_injective hcb hc).comp joinSegments_injective

theorem length_segmentString (cb : Option Γ → BitString c) (X : σ → List Γ) :
    (segmentString cb X).length = (∑ s, (X s).length + Fintype.card σ) * c := by
  rw [segmentString, length_bitsOf, length_joinSegments]

/-- The number of units of the bit strings from a party to all parties (or to a party from all
parties), if the party writes (or reads) at most `T` letters on all tapes together. -/
theorem sum_unitCount_le {A T ub : ℕ} {cb : Option Γ → BitString c} {X : σ → Fin A → List Γ}
    (h : ∑ s, (cat (X s)).length ≤ T) :
    ∑ b, unitCount ub (segmentString cb fun s => X s b) ≤
      (T + A * Fintype.card σ) * c / ub + A := by
  simp only [unitCount, length_segmentString, sum_add_distrib, sum_const, card_univ,
    Fintype.card_fin, smul_eq_mul, mul_one]
  refine Nat.add_le_add_right ((Nat.sum_div_le_sum_div _ _ _).trans (Nat.div_le_div_right ?_)) _
  rw [← sum_mul, sum_add_distrib, sum_comm]
  simp only [sum_length_cat, sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
  exact Nat.mul_le_mul_right _ (Nat.add_le_add_right h _)

end Strings

variable {F Γ S Q : Type*} {A K : ℕ}

/-- What a block emits, if `R s b` is what it writes for the party `b` on the tape `s` and
`C s b` is what it reads from the party `b` on the tape `s`. The tape `none` is the input, which
a block only reads. -/
@[expose] def blockEmission (R C : Option S → Fin A → List Γ) : Ch S Unit → List Γ
  | .tp s false => cat (R (some s))
  | .tp s true => cat (C (some s))
  | .inp _ => cat (C none)

/-- The parts of a word, of `ℓ` letters each: the part `κ` begins at the letter `κ * ℓ`. -/
@[expose] def parts (ℓ : ℕ) (u : List Γ) (κ : Fin K) : List Γ := (u.drop (κ * ℓ)).take ℓ

/-- The first `K` parts of a word concatenate to its first `K * ℓ` letters. -/
theorem cat_parts (ℓ : ℕ) (u : List Γ) :
    cat (parts ℓ u : Fin K → List Γ) = u.take (K * ℓ) := by
  induction K generalizing u with
  | zero => simp [cat]
  | succ K ih =>
    have e : (fun κ : Fin K => parts ℓ u κ.succ) = parts ℓ (u.drop ℓ) := by
      funext κ
      simp [parts, Nat.add_mul, Nat.add_comm]
    rw [cat_succ, e, ih, Nat.succ_mul, Nat.add_comm (K * ℓ), List.take_add]
    simp [parts]

theorem length_parts_le (ℓ : ℕ) (u : List Γ) (κ : Fin K) : (parts ℓ u κ).length ≤ ℓ := by
  simp [parts]

/-- What the parties write on the tapes, if the blocks emit `v` and the input parties hold
`x`. -/
private def written (x : Fin K → List Γ) (v : Fin K → Ch S Unit → List Γ) :
    Option S → Fin (K + K) → List Γ
  | none => Fin.append (fun _ => []) x
  | some s => Fin.append (fun κ => v κ (.tp s false)) fun _ => []

/-- What the parties read from the tapes, if the blocks emit `v`. -/
private def read (v : Fin K → Ch S Unit → List Γ) : Option S → Fin (K + K) → List Γ
  | none => Fin.append (fun κ => v κ (.inp ())) fun _ => []
  | some s => Fin.append (fun κ => v κ (.tp s true)) fun _ => []

private theorem cat_written_eq_cat_read_iff {x : Fin K → List Γ}
    {v : Fin K → Ch S Unit → List Γ} {u : Unit → List Γ} (hu : cat x = u ()) :
    (∀ s, cat (written x v s) = cat (read v s)) ↔
      (∀ s, cat (fun k => v k (.tp s false)) = cat fun k => v k (.tp s true)) ∧
        ∀ j, cat (fun k => v k (.inp j)) = u j := by
  have hnil : cat (fun _ : Fin K => ([] : List Γ)) = [] := cat_eq_nil.2 fun _ => rfl
  simp only [Option.forall, written, read, cat_add, Fin.append_left, Fin.append_right, hnil, hu,
    List.nil_append, List.append_nil]
  exact and_comm.trans (and_congr_right fun _ => ⟨fun h _ => h.symm, fun h => (h ()).symm⟩)

private theorem length_written_le {T : ℕ} {x : Fin K → List Γ} (hx : ∀ κ, (x κ).length ≤ T)
    {v : Fin K → Ch S Unit → List Γ} (hv : ∀ κ z, (v κ z).length ≤ T) (s : Option S)
    (a : Fin (K + K)) :
    (written x v s a).length ≤ T := by
  cases s <;> induction a using Fin.addCases <;>
    simp [written, hx, hv, -Fin.natAdd_eq_addNat]

variable [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S] [Fintype Q] [DecidableEq Q]

section Party

variable [Semiring F] {mu : Letter S Unit Γ → Matrix Q Q F} {T : ℕ} {q : Fin (K + 1) → Q}
  {x : Fin K → List Γ} {R C : Option S → Fin (K + K) → List Γ}

/-- The weight of what the party `p` writes for the parties `b` on the tapes `s`, `R s b`, and
reads from them, `C s b`. A block `Fin.castAdd K κ` does not write on the input tape `none`, and
has the weight of a block from the state `q κ` to the state `q (κ + 1)`. An input party
`Fin.natAdd K κ` writes its part `x κ` of the input on the input tape and nothing else, reads
nothing, and has the weight `1`. -/
def partyWeight (mu : Letter S Unit Γ → Matrix Q Q F) (T : ℕ) (q : Fin (K + 1) → Q)
    (x : Fin K → List Γ) (p : Fin (K + K)) (R C : Option S → Fin (K + K) → List Γ) : F :=
  Fin.append
    (fun κ => if ∀ b, R none b = [] then
      blockWeight mu T (q κ.castSucc) (q κ.succ) (blockEmission R C) else 0)
    (fun κ => if (∀ s b, R (some s) b = []) ∧ (∀ s b, C s b = []) ∧ cat (R none) = x κ then 1
      else 0) p

theorem partyWeight_block (κ : Fin K) : partyWeight mu T q x (Fin.castAdd K κ) R C =
    if ∀ b, R none b = [] then
      blockWeight mu T (q κ.castSucc) (q κ.succ) (blockEmission R C) else 0 :=
  Fin.append_left _ _ κ

theorem partyWeight_input (κ : Fin K) : partyWeight mu T q x (Fin.natAdd K κ) R C =
    if (∀ s b, R (some s) b = []) ∧ (∀ s b, C s b = []) ∧ cat (R none) = x κ then 1 else 0 :=
  Fin.append_right _ _ κ

/-- A party writes at most `T` letters on all tapes together. -/
theorem sum_length_le_of_partyWeight_ne_zero (hx : ∀ κ, (x κ).length ≤ T) {p : Fin (K + K)}
    (h : partyWeight mu T q x p R C ≠ 0) : ∑ s, (cat (R s)).length ≤ T := by
  rw [Fintype.sum_option]
  induction p using Fin.addCases with
  | left κ =>
    rw [partyWeight_block] at h
    obtain ⟨hR, hw⟩ := ite_ne_right_iff.1 h
    rw [cat_eq_nil.2 hR, List.length_nil, zero_add]
    refine le_trans ?_ (sum_length_le_of_blockWeight_ne_zero hw)
    exact (sum_map univ ⟨fun s => Ch.tp s false, fun _ _ e => by simpa using e⟩
      fun z => (blockEmission R C z).length).symm.trans_le (sum_le_sum_of_subset (subset_univ _))
  | right κ =>
    rw [partyWeight_input] at h
    obtain ⟨⟨h1, -, h3⟩, -⟩ := ite_ne_right_iff.1 h
    simpa [h3, fun s => cat_eq_nil.2 (h1 s)] using hx κ

end Party

section Segments

variable [CommSemiring F] {mu : Letter S Unit Γ → Matrix Q Q F} {T : ℕ} {q : Fin (K + 1) → Q}
  {x : Fin K → List Γ} {X : Option S → Fin (K + K) → Fin (K + K) → List Γ}

/-- The product of the weights of the parties, for the segments `X s a b` that the party `a`
writes on the tape `s` and the party `b` reads. -/
@[expose] def segmentWeight (mu : Letter S Unit Γ → Matrix Q Q F) (T : ℕ) (q : Fin (K + 1) → Q)
    (x : Fin K → List Γ) (X : Option S → Fin (K + K) → Fin (K + K) → List Γ) : F :=
  ∏ p, partyWeight mu T q x p (fun s b => X s p b) (fun s b => X s b p)

/-- The segments of at most `T` letters each, between `K + K` parties on the tapes `S` and the
input. -/
noncomputable def segments (Γ S : Type*) [Fintype Γ] [Fintype S] [DecidableEq S] (K T : ℕ) :
    Finset (Option S → Fin (K + K) → Fin (K + K) → List Γ) :=
  Fintype.piFinset fun _ => Fintype.piFinset fun _ => Fintype.piFinset fun _ => List.wordsLe Γ T

omit [DecidableEq Γ] in
@[simp] theorem mem_segments : X ∈ segments Γ S K T ↔ ∀ s a b, (X s a b).length ≤ T := by
  simp [segments]

private theorem segmentWeight_eq_prod (h1 : ∀ κ b, X none (Fin.castAdd K κ) b = [])
    (h2 : ∀ s κ b, X (some s) (Fin.natAdd K κ) b = []) (h3 : ∀ s κ b, X s b (Fin.natAdd K κ) = [])
    (h4 : ∀ κ, cat (X none (Fin.natAdd K κ)) = x κ) :
    segmentWeight mu T q x X = ∏ κ : Fin K, blockWeight mu T (q κ.castSucc) (q κ.succ)
      (blockEmission (fun s b => X s (Fin.castAdd K κ) b) fun s b => X s b (Fin.castAdd K κ)) := by
  simp [segmentWeight, Fin.prod_univ_add, partyWeight_block, partyWeight_input, h1, h2, h3, h4,
    -Fin.natAdd_eq_addNat]

/-- If the product of the weights of the parties does not vanish, then the blocks write nothing
on the input tape, the input parties write only their parts of the input, nothing is written for
the input parties, and the product is the product of the weights of the blocks. -/
private theorem segmentWeight_ne_zero (h : segmentWeight mu T q x X ≠ 0) :
    (∀ κ b, X none (Fin.castAdd K κ) b = []) ∧
    (∀ s κ b, X (some s) (Fin.natAdd K κ) b = []) ∧ (∀ s κ b, X s b (Fin.natAdd K κ) = []) ∧
    (∀ κ, cat (X none (Fin.natAdd K κ)) = x κ) ∧
    segmentWeight mu T q x X = ∏ κ : Fin K, blockWeight mu T (q κ.castSucc) (q κ.succ)
      (blockEmission (fun s b => X s (Fin.castAdd K κ) b) fun s b => X s b (Fin.castAdd K κ)) := by
  have h0 (p) : partyWeight mu T q x p (fun s b => X s p b) (fun s b => X s b p) ≠ 0 :=
    fun hp => h (prod_eq_zero (mem_univ p) hp)
  have hb (κ : Fin K) := h0 (Fin.castAdd K κ)
  have hi (κ : Fin K) := h0 (Fin.natAdd K κ)
  simp only [partyWeight_block, partyWeight_input, ite_ne_right_iff] at hb hi
  exact ⟨fun κ => (hb κ).1, fun s κ => (hi κ).1.1 s, fun s κ => (hi κ).1.2.1 s,
    fun κ => (hi κ).1.2.2, segmentWeight_eq_prod (fun κ => (hb κ).1) (fun s κ => (hi κ).1.1 s)
      (fun s κ => (hi κ).1.2.1 s) fun κ => (hi κ).1.2.2⟩

/-- The segments of non-vanishing weight with staircase support are the common refinement of what
the parties write and read. -/
private theorem isRef_of_segmentWeight_ne_zero (hst : ∀ s, Stair (X s))
    (h : segmentWeight mu T q x X ≠ 0) (s : Option S) :
    IsRef (written x (fun κ => blockEmission (fun s b => X s (Fin.castAdd K κ) b)
      fun s b => X s b (Fin.castAdd K κ)) s) (read (fun κ => blockEmission
      (fun s b => X s (Fin.castAdd K κ) b) fun s b => X s b (Fin.castAdd K κ)) s) (X s) := by
  obtain ⟨h1, h2, h3, h4, -⟩ := segmentWeight_ne_zero h
  refine ⟨hst s, ?_, ?_⟩ <;> cases s <;>
    simp [Fin.forall_fin_add, written, read, blockEmission, cat_eq_nil, h1, h2, h3, h4,
      -Fin.natAdd_eq_addNat]

/-- A common refinement of what the parties write and read consists of segments whose blocks emit
`v`, and its weight is the product of the weights of the blocks. -/
private theorem segmentWeight_of_isRef {v : Fin K → Ch S Unit → List Γ}
    (h : ∀ s, IsRef (written x v s) (read v s) (X s)) :
    (fun κ => blockEmission (fun s b => X s (Fin.castAdd K κ) b)
      fun s b => X s b (Fin.castAdd K κ)) = v ∧
    segmentWeight mu T q x X = ∏ κ, blockWeight mu T (q κ.castSucc) (q κ.succ) (v κ) := by
  have row (s a) := (h s).row a
  have col (s b) := (h s).col b
  have hv : (fun κ => blockEmission (fun s b => X s (Fin.castAdd K κ) b)
      fun s b => X s b (Fin.castAdd K κ)) = v := by
    funext κ z
    rcases z with ⟨s, _ | _⟩ | ⟨⟨⟩⟩
    · exact (row (some s) (Fin.castAdd K κ)).trans (Fin.append_left _ _ κ)
    · exact (col (some s) (Fin.castAdd K κ)).trans (Fin.append_left _ _ κ)
    · exact (col none (Fin.castAdd K κ)).trans (Fin.append_left _ _ κ)
  refine ⟨hv, ?_⟩
  rw [segmentWeight_eq_prod
    (fun κ => cat_eq_nil.1 ((row none (Fin.castAdd K κ)).trans (Fin.append_left _ _ κ)))
    (fun s κ => cat_eq_nil.1 ((row (some s) (Fin.natAdd K κ)).trans (Fin.append_right _ _ κ)))
    (fun s κ => cat_eq_nil.1 ((col s (Fin.natAdd K κ)).trans
      (by cases s <;> exact Fin.append_right _ _ κ)))
    fun κ => (row none (Fin.natAdd K κ)).trans (Fin.append_right _ _ κ)]
  exact prod_congr rfl fun κ _ => by rw [← hv]

/-- **Segments.** For given states `q` between the blocks, the sum over the words that the
blocks emit, restricted to those for which the two sides of every tape carry the same
concatenation and the input channel carries the concatenation of the parts `x` of the input, is
the sum over the segments with staircase support, of the product of the weights of the
parties. -/
theorem sum_segments (q : Fin (K + 1) → Q) {x : Fin K → List Γ} (hx : ∀ κ, (x κ).length ≤ T)
    (u : Unit → List Γ) (hu : cat x = u ()) :
    (∑ v ∈ Fintype.piFinset fun _ : Fin K => Fintype.piFinset fun _ : Ch S Unit =>
        List.wordsLe Γ T,
      if (∀ s, cat (fun k => v k (.tp s false)) = cat fun k => v k (.tp s true)) ∧
        ∀ j, cat (fun k => v k (.inp j)) = u j then
      ∏ k, blockWeight mu T (q k.castSucc) (q k.succ) (v k) else 0) =
    ∑ X ∈ segments Γ S K T, if ∀ s, Stair (X s) then segmentWeight mu T q x X else 0 := by
  symm
  refine sum_bij_ne_zero (fun X _ _ κ => blockEmission (fun s b => X s (Fin.castAdd K κ) b)
    fun s b => X s b (Fin.castAdd K κ)) ?_ ?_ ?_ ?_
  · intro X _ hX
    obtain ⟨-, hw⟩ := ite_ne_right_iff.1 hX
    rw [(segmentWeight_ne_zero hw).2.2.2.2] at hw
    exact Fintype.mem_piFinset.2 fun κ => Fintype.mem_piFinset.2
      (blockWeight_ne_zero fun h0 => hw (prod_eq_zero (mem_univ κ) h0))
  · intro X _ hX X' _ hX' heq
    obtain ⟨hst, hw⟩ := ite_ne_right_iff.1 hX
    obtain ⟨hst', hw'⟩ := ite_ne_right_iff.1 hX'
    exact funext fun s => (isRef_of_segmentWeight_ne_zero hst hw s).unique
      (heq ▸ isRef_of_segmentWeight_ne_zero hst' hw' s)
  · intro v hv hne
    obtain ⟨hm, hw⟩ := ite_ne_right_iff.1 hne
    choose X hX using fun s => IsRef.exists ((cat_written_eq_cat_read_iff hu).2 hm s)
    obtain ⟨e, hW⟩ := segmentWeight_of_isRef (mu := mu) (T := T) (q := q) hX
    refine ⟨X, mem_segments.2 fun s a b => ?_, ?_, e⟩
    · rw [Fintype.mem_piFinset] at hv
      exact (length_le_cat (X s a) b).trans ((hX s).row a ▸ length_written_le hx
        (fun κ z => List.mem_wordsLe.1 (Fintype.mem_piFinset.1 (hv κ) z)) s a)
    · rwa [ite_eq_left fun s => (hX s).stair, hW]
  · intro X _ hX
    obtain ⟨hst, hw⟩ := ite_ne_right_iff.1 hX
    rw [ite_eq_left hst, ite_eq_left ((cat_written_eq_cat_read_iff hu).1 fun s =>
      (isRef_of_segmentWeight_ne_zero hst hw s).cat_eq), (segmentWeight_ne_zero hw).2.2.2.2]

end Segments

end Cslib.Circuits.Arithmetic.Separation.Cut
