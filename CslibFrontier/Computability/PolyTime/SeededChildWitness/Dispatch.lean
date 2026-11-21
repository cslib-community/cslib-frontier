/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.SeededChildWitness.Fields
public import CslibFrontier.Computability.PolyTime.SeededRankChallenge
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Sum

/-!
# Routing a shared child witness to one verification branch

After the nine proposed fields, three universal moves select the arithmetic check, the parent
endpoint check, or one of six count checks. The last moves challenge a bit of the selected
count. An out-of-width bit index accepts immediately. Every count request retains the edge
and the two endpoints from the original existential prefix.
-/

public section

namespace Cslib.SeededChildWitness.Dispatch

open Turing.MultiTapeTM ComputableInPolyTime BitString

/-- A vertex prefix, a port prefix, or a packing rank at the supplied parent edge. -/
abbrev Count := ℕ ⊕ ((Bool × ℕ) ⊕ (ℕ × (ℕ × ℕ)))

/-- All endpoint keys and prefix bounds are binary. -/
abbrev encCount := encSum encNat (encSum (encPair encBool encNat) (encPair encNat
  (encPair encNat encNat)))

/-- The count request, challenged bit index, and bit of the previously guessed count. -/
abbrev BitQuery := Count × (ℕ × Bool)

/-- Framed count and bit index, followed by the claimed bit. -/
abbrev encBitQuery := encPair encCount (encPair encNat encBool)

/-- A left tag selects local arithmetic (`false`) or the parent endpoint (`true`). A right
tag is a padded index (`none`) or one genuine count-bit request. -/
abbrev Branch := Bool ⊕ Option BitQuery

/-- Encodings of the finite control and of its single optional count request. -/
abbrev encBranch := encSum encBool (encOption encBitQuery)

/-- Short metadata for the parent size, coordinate's vertex universe, and selected child edge. -/
structure Public where
  edges : ℕ
  vertices : ℕ
  child : ℕ

/-- Three binary integers. -/
enc_structure encPublic : Public where edges : encNat, vertices : encNat, child : encNat

/-- Pair the selected count request with its proposed value. -/
@[expose] def selected (b : Public) (p : Proposal) (s : ℕ) : Count × ℕ :=
  let c := p.counts
  if s = 2 then (.inr (.inl (false, p.edge)), c.rowPrefix)
  else if s = 3 then (.inr (.inl (true, p.edge)), c.colPrefix)
  else if s = 4 then (.inr (.inl (false, b.edges)), c.rowTotal)
  else if s = 5 then
    (.inl (if b.child < c.rowTotal then p.ends.1 else p.ends.2), c.vertexPrefix)
  else if s = 6 then (.inl b.vertices, c.vertexTotal)
  else (.inr (.inr (p.edge, p.ends)), c.classRank)

/-- Select exactly one branch. The tested bit index is clamped before converting to unary
so that the machine also runs in polynomial time on arbitrary external words. -/
@[expose] def branch (b : Public) (p : Proposal) (w s j : ℕ) : Branch :=
  if s = 0 then .inl false
  else if s = 1 then .inl true
  else if j < w then
    let pair := selected b p s
    .inr (some (pair.1, j, pair.2.testBit (min w j)))
  else .inr none

/-- Binary width used by all nine proposed fields. -/
@[expose] def width (b : Public) : ℕ := (max b.edges b.vertices).size

/-- After the common nine-field prefix, decode the low three selector bits and the bit index. -/
@[expose] def run (x : Public × List Bool) : Proposal × Branch :=
  let w := width x.1
  let p := parse w x.2
  let rest := x.2.drop (9 * w)
  (p, branch x.1 p w (ofBits (rest.take 3)) (ofBits (rest.drop 3)))

/-- Correct concatenation of all three phases, including a zero bit-index width. -/
theorem run_word (b : Public) (p : Proposal) (s : Fin 8) (j : Fin (2 ^ Nat.clog 2 (width b)))
    (hp : ∀ n ∈ p.fields, n < 2 ^ width b) :
    run (b, word (width b) p ++ (lowBits 3 s.val ++ lowBits (Nat.clog 2 (width b)) j.val)) =
      (p, branch b p (width b) s.val j.val) := by
  have hs : s.val < 2 ^ 3 := s.isLt
  have hd (tail : List Bool) : (word (width b) p ++ tail).drop (9 * width b) = tail := by
    rw [← length_word (width b) p]
    exact List.drop_left
  simp [run, parse_word _ _ hp, hd, ofBits_eq_lsbValue,
    lsbValue_lowBits hs, lsbValue_lowBits j.isLt]

private theorem field_append (i w : ℕ) (xs tail : List Bool) (hlen : (i + 1) * w ≤ xs.length) :
    field i w (xs ++ tail) = field i w xs := by
  induction i generalizing xs with
  | zero => simp [field, List.take_append_of_le_length (by simpa using hlen : w ≤ xs.length)]
  | succ i ih =>
    have hw : w ≤ xs.length := by nlinarith
    change field i w ((xs ++ tail).drop w) = field i w (xs.drop w)
    rw [List.drop_append_of_le_length hw]
    apply ih
    rw [List.length_drop]
    rw [Nat.add_mul, Nat.one_mul] at hlen
    omega

/-- Bits following any complete nine-field prefix leave its parsed proposal unchanged. -/
theorem parse_append (w : ℕ) (xs tail : List Bool) (h : xs.length = 9 * w) :
    parse w (xs ++ tail) = parse w xs := by
  have hf (i : ℕ) (hi : i < 9) : field i w (xs ++ tail) = field i w xs :=
    field_append i w xs tail (h ▸ Nat.mul_le_mul_right w hi)
  simp only [parse, hf 0 (by decide), hf 1 (by decide), hf 2 (by decide), hf 3 (by decide),
    hf 4 (by decide), hf 5 (by decide), hf 6 (by decide), hf 7 (by decide), hf 8 (by decide)]

/-- Route every complete prefix exactly, including existential choices on a rejecting branch. -/
theorem run_prefix (b : Public) (xs : List Bool) (hlen : xs.length = 9 * width b)
    (s : Fin 8) (j : Fin (2 ^ Nat.clog 2 (width b))) :
    run (b, xs ++ (lowBits 3 s.val ++ lowBits (Nat.clog 2 (width b)) j.val)) =
      (parse (width b) xs, branch b (parse (width b) xs) (width b) s.val j.val) := by
  have hd (tail : List Bool) : (xs ++ tail).drop (9 * width b) = tail := by
    rw [← hlen]; exact List.drop_left
  have hs : s.val < 2 ^ 3 := s.isLt
  simp [run, parse_append _ _ _ hlen, hd, ofBits_eq_lsbValue,
    lsbValue_lowBits hs, lsbValue_lowBits j.isLt]

private abbrev encPorts := encPair encBool encNat
private abbrev encPack := encPair encNat (encPair encNat encNat)

private theorem selected_polyTime {α : Type} {enc : α ↪ List Bool} {b : α → Public}
    {p : α → Proposal} {s : α → ℕ} (hb : ComputableInPolyTime b enc encPublic)
    (hp : ComputableInPolyTime p enc encProposal) (hs : ComputableInPolyTime s enc encNat) :
    ComputableInPolyTime (fun x => selected (b x) (p x) (s x)) enc (encPair encCount encNat) := by
  let port := (sumInr encNat (encSum encPorts encPack)).comp (sumInl encPorts encPack)
  let pack := (sumInr encNat (encSum encPorts encPack)).comp (sumInr encPorts encPack)
  let vertex := sumInl encNat (encSum encPorts encPack)
  have he := encProposal_edge_polyTime hp
  have hend := encProposal_ends_polyTime hp
  have hc := encProposal_counts_polyTime hp
  have hrt := encCounts_rowTotal_polyTime hc
  have hv := ite_decide (binary_lt' (encPublic_child_polyTime hb) hrt) hend.fst' hend.snd'
  let his (n : ℕ) := decide_eq' hs (const n)
  exact ite_decide (his 2)
    ((port.comp ((const false).prod he)).prod (encCounts_rowPrefix_polyTime hc))
    (ite_decide (his 3) ((port.comp ((const true).prod he)).prod (encCounts_colPrefix_polyTime hc))
      (ite_decide (his 4) ((port.comp ((const false).prod (encPublic_edges_polyTime hb))).prod hrt)
        (ite_decide (his 5) ((vertex.comp hv).prod (encCounts_vertexPrefix_polyTime hc))
          (ite_decide (his 6) ((vertex.comp (encPublic_vertices_polyTime hb)).prod
            (encCounts_vertexTotal_polyTime hc)) ((pack.comp (he.prod hend)).prod
              (encCounts_classRank_polyTime hc))))))

private theorem branch_polyTime {α : Type} {enc : α ↪ List Bool} {b : α → Public}
    {p : α → Proposal} {w s j : α → ℕ} (hb : ComputableInPolyTime b enc encPublic)
    (hp : ComputableInPolyTime p enc encProposal) (hw : ComputableInPolyTime w enc encUnary)
    (hs : ComputableInPolyTime s enc encNat) (hj : ComputableInPolyTime j enc encNat) :
    ComputableInPolyTime (fun x => branch (b x) (p x) (w x) (s x) (j x)) enc encBranch := by
  have h := selected_polyTime hb hp hs
  have hbit := binary_testBit h.snd' (binary_min_unary' hw hj)
  have hq := (sumInr encBool (encOption encBitQuery)).comp
    ((optionSome encBitQuery).comp (h.fst'.prod (hj.prod hbit)))
  exact ite_decide (decide_eq' hs (const 0)) (const (encOut := encBranch) (Sum.inl false))
    (ite_decide (decide_eq' hs (const 1)) (const (encOut := encBranch) (Sum.inl true))
      (ite_decide (binary_lt' hj (unary_to_binary.comp hw)) hq
        (const (encOut := encBranch) (Sum.inr none))))

/-- Compute the common field width in unary from the supplied binary universe sizes. -/
theorem computableInPolyTime_width : ComputableInPolyTime width encPublic encUnary := by
  have he := encPublic_edges_deg.computableInPolyTime
  have hv := encPublic_vertices_deg.computableInPolyTime
  have hm := ite_decide (binary_lt' he hv) hv he
  exact (binary_size.comp hm).of_enc_eq fun x => by
    dsimp [Function.comp_def, width]
    split_ifs with h
    · rw [Nat.max_eq_right h.le]
    · rw [Nat.max_eq_left (Nat.le_of_not_gt h)]

/-- A single finite deterministic machine parses the common proposal and the entire challenge.
Its time is polynomial in the binary graph parameters and the actual choice word. -/
theorem computableInPolyTime_run : ComputableInPolyTime run (encPair encPublic encBits)
    (encPair encProposal encBranch) := by
  have hb := fst encPublic encBits
  have hx := snd encPublic encBits
  have hw := computableInPolyTime_width.comp hb
  have hp := computableInPolyTime_parse.comp (hw.prod hx)
  have hr := bitsDropWithInput hx (unary_mul' (const 9) hw)
  have hs := bitsToNat.comp (bitsTakeWithInput hr (const 3))
  have hj := bitsToNat.comp (bitsDropWithInput hr (const 3))
  exact hp.prod (branch_polyTime hb hp hw hs hj)

end Cslib.SeededChildWitness.Dispatch
