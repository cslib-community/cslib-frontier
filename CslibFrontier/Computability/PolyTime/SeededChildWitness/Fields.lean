/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.SeededChildWitness
public import CslibFrontier.Computability.PolyTime.SeedChoice

/-!
# Binary fields of a parent-edge witness

One existential prefix chooses a parent edge, its two endpoints, and six counts. All nine
fields have the same width. The final count and endpoint checks can branch after this word is
fixed. The native decoder ignores all bits after the nine fields.
-/

public section
namespace Cslib.SeededChildWitness

open Turing.MultiTapeTM ComputableInPolyTime BitString

/-- The part of a child endpoint request that is guessed on a common existential branch. -/
structure Proposal where
  edge : ℕ
  ends : ℕ × ℕ
  counts : Counts

/-- The returned edge index, endpoints and counts are binary integers. -/
enc_structure encProposal : Proposal where edge : encNat, ends : (encPair encNat encNat),
  counts : encCounts

/-- Read the indicated fixed-width field from a choice tape. -/
@[expose] def field : ℕ → ℕ → List Bool → ℕ
  | 0, w, bits => ofBits (bits.take w)
  | i + 1, w, bits => field i w (bits.drop w)

/-- Decode the nine fields, with zero padding on shorter words. -/
@[expose] def parse (w : ℕ) (bits : List Bool) : Proposal :=
  let f := fun i => field i w bits
  ⟨f 0, (f 1, f 2), ⟨f 3, f 4, f 5, f 6, f 7, f 8⟩⟩

/-- Recover the natural numbers in tape order. -/
@[expose] def Proposal.fields (p : Proposal) : List ℕ :=
  [p.edge, p.ends.1, p.ends.2, p.counts.rowPrefix, p.counts.colPrefix, p.counts.rowTotal,
    p.counts.vertexPrefix, p.counts.vertexTotal, p.counts.classRank]

/-- Write each number least significant bit first. -/
@[expose] def word (w : ℕ) (p : Proposal) : List Bool := p.fields.flatMap (lowBits w)

@[simp] theorem length_word (w : ℕ) (p : Proposal) : (word w p).length = 9 * w := by
  simp [word, Proposal.fields]
  omega

/-- Parsing an arbitrary choice tape always gives bounded binary fields. -/
theorem parse_fields_lt (w : ℕ) (bits : List Bool) :
    ∀ n ∈ (parse w bits).fields, n < 2 ^ w := by
  have hf (i : ℕ) (xs : List Bool) : field i w xs < 2 ^ w := by
    induction i generalizing xs with
    | zero =>
      simp only [field, ofBits_eq_lsbValue]
      exact (lsbValue_lt _).trans_le
        (Nat.pow_le_pow_right (by decide : 0 < 2) (List.length_take_le _ _))
    | succ i ih => exact ih _
  simp [parse, Proposal.fields, hf]

/-- A bounded proposal round-trips exactly, regardless of subsequent player moves. -/
theorem parse_word (w : ℕ) (p : Proposal) (h : ∀ n ∈ p.fields, n < 2 ^ w) (tail : List Bool) :
    parse w (word w p ++ tail) = p := by
  rcases p with ⟨e, ⟨r, c⟩, ⟨pr, pc, rt, vp, vt, cr⟩⟩
  simp only [Proposal.fields, List.forall_mem_cons] at h
  rcases h with ⟨h₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, _⟩
  simp [parse, field, word, Proposal.fields, List.append_assoc,
    ofBits_eq_lsbValue, lsbValue_lowBits, h₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈]

private theorem field_polyTime (i : ℕ) {α : Type} {enc : α ↪ List Bool}
    {width : α → ℕ} (hw : ComputableInPolyTime width enc encUnary) {bits : α → List Bool}
    (hb : ComputableInPolyTime bits enc encBits) :
    ComputableInPolyTime (fun x => field i (width x) (bits x)) enc encNat := by
  induction i generalizing bits with
  | zero => exact bitsToNat.comp (bitsTakeWithInput hb hw)
  | succ i ih => exact ih (bitsDropWithInput hb hw)

/-- A finite deterministic machine extracts all nine binary numbers using a runtime unary width. -/
theorem computableInPolyTime_parse : ComputableInPolyTime (Function.uncurry parse)
    (encPair encUnary encBits) encProposal := by
  let hf (i : ℕ) := field_polyTime i (fst encUnary encBits) (snd encUnary encBits)
  exact encProposal_mk_polyTime (hf 0) ((hf 1).prod (hf 2))
    (encCounts_mk_polyTime (hf 3) (hf 4) (hf 5) (hf 6) (hf 7) (hf 8))

end Cslib.SeededChildWitness
