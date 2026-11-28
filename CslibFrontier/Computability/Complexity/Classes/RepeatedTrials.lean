/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
public import Mathlib.Algebra.Polynomial.Eval.Defs
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Lists
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Degree.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Foundations.Data.List.OfFn
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Deterministic computations on repeated random-tape blocks

Split a supplied bit list into fixed-width rows and collect one output per row. Callers
can compute the dimensions from the encoded instance length. Missing bits read as `false`;
extra bits are ignored, and zero-width rows are retained. No probability distribution or
complexity-class error condition is imposed here.

`repeatAny` and `repeatMajority` aggregate the same votes. Their error bounds belong to the
class-specific amplification modules. `CslibFrontier.Computability.Probabilistic.Repeat` provides
the separate probabilistic-program interface for independently sampled runs.

## Main definitions

* `Cslib.Complexity.repeatOutputs` and `Cslib.Complexity.repeatVotes`: collect ordered outputs
  or Boolean votes.
* `Cslib.Complexity.repeatAny`: accept if any vote is `true`.
* `Cslib.Complexity.repeatMajority`: accept if more than half of `2 r(n)` votes are `true`.

## Main results

* `Cslib.Complexity.repeatVotes_ofFn`: votes on a full tape agree with finite block evaluation.
* `Cslib.Complexity.computableInO_repeatOutputs` and
  `Cslib.Complexity.computableInO_repeatVotes`: runtime bounds for varying unary dimensions and
  arbitrary verifier clocks.
* `Cslib.Complexity.computableInPolyTime_repeatVotes`: producing votes takes polynomial time.
* `Cslib.Complexity.computableInPolyTime_repeatAny`,
  `Cslib.Complexity.computableInPolyTime_repeatMajority`: efficient aggregation.

## References

Extracted from the deterministic repetition implementations in `BPP.Amplification` and `RP` by
Samuel Schlesinger. For their use in error reduction, see
[S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Chapter 7][AroraBarak09].
-/

@[expose] public section

namespace Cslib.Complexity

open Finset Turing.MultiTapeTM

variable {α : Type}

/-- Collect outputs on fixed-width rows of a supplied random tape, padding missing bits with
`false` and ignoring bits beyond the prescribed rows. Zero-width rows still contribute outputs. -/
def repeatOutputs {β : Type} (trials width : ℕ) (evaluate : α × List Bool → β)
    (input : α × List Bool) : List β :=
  (BitString.listRows trials width input.2).map (fun row => evaluate (input.1, row))

/-- Repetition produces one output for each prescribed trial, even on a short tape. -/
@[simp]
theorem length_repeatOutputs {β : Type} (trials width : ℕ) (V : α × List Bool → β)
    (input : α × List Bool) : (repeatOutputs trials width V input).length = trials := by
  simp [repeatOutputs]

/-- Collect Boolean votes on fixed-width rows of a supplied random tape. -/
def repeatVotes (trials width : ℕ) (V : α × List Bool → Bool) (input : α × List Bool) : List Bool :=
  repeatOutputs trials width V input

/-- Repetition produces one vote for each prescribed trial, even on a short tape. -/
@[simp]
theorem length_repeatVotes (trials width : ℕ) (V : α × List Bool → Bool)
    (input : α × List Bool) : (repeatVotes trials width V input).length = trials :=
  length_repeatOutputs trials width V input

/-- On a full tape, votes are evaluations on its finite blocks, in order. -/
theorem repeatVotes_ofFn {trials width : ℕ} {V : α × List Bool → Bool} (a : α)
    (x : BitString (trials * width)) :
    repeatVotes trials width V (a, List.ofFn x) =
      List.ofFn (fun i => V (a, List.ofFn (BitString.block x i))) := by
  simp [repeatVotes, repeatOutputs, BitString.listRows_ofFn, List.map_ofFn, Function.comp_def]

/-- Producing votes takes polynomial time when the verifier and the unary dimensions do.
The dimensions may depend on the complete input, and output uses the raw bit-list encoding. -/
@[fun_prop]
theorem computableInPolyTime_repeatVotes {enc : α ↪ List Bool}
    {V : α × List Bool → Bool} {trials width : α × List Bool → ℕ}
    (hV : ComputableInPolyTime V (encPair enc encBits) encBool)
    (htrials : ComputableInPolyTime trials (encPair enc encBits) encUnary)
    (hwidth : ComputableInPolyTime width (encPair enc encBits) encUnary) :
    ComputableInPolyTime (fun input => repeatVotes (trials input) (width input) V input)
      (encPair enc encBits) encBits := by
  unfold repeatVotes repeatOutputs
  fun_prop

/-- Collecting framed outputs charges polynomial overhead for the input and unary dimensions
and at most one verifier call per row. The clock includes the time to handle the framed output
list. Only the verifier times on rows of the prescribed width must be bounded. -/
theorem computableInO_repeatOutputs {β : Type} {enc : α ↪ List Bool} {encOut : β ↪ List Bool}
    {V : α × List Bool → β} {trials width : α × List Bool → ℕ}
    {Tv Sv Ttr Str Tw Sw R : α × List Bool → ℕ}
    (hV : ComputableInO V (encPair enc encBits) encOut Tv Sv)
    (htr : ComputableInO trials (encPair enc encBits) encUnary Ttr Str)
    (hw : ComputableInO width (encPair enc encBits) encUnary Tw Sw)
    (hR : ∀ p row, row.length = width p → Tv (p.1, row) ≤ R p) :
    let outputs (p : α × List Bool) := repeatOutputs (trials p) (width p) V p
    ∃ d S, ComputableInO outputs (encPair enc encBits) (encList encOut)
      (fun p => (trials p + 1) *
        (((encPair enc encBits p).length + Ttr p + Tw p + 1) ^ d +
          (encList encOut (outputs p)).length + R p)) S := by
  dsimp only
  let input := encPair enc encBits
  let prepared := encPair (encPair encUnary encUnary) encBits
  let prep (p : α × List Bool) := ((trials p, width p), p.2)
  let rows (p : α × List Bool) := BitString.listRows (trials p) (width p) p.2
  let base (p : α × List Bool) := (input p).length + Ttr p + Tw p + 1
  have hprep : ComputableInO prep input prepared
      (fun p => Ttr p + Tw p + (input p).length)
      (fun p => Str p + Sw p + (input p).length) :=
    (htr.prod hw).prod (ComputableInO.snd enc encBits)
  have hsplit : ComputableInPolyTime
      (fun p : (ℕ × ℕ) × List Bool => BitString.listRows (Prod.fst p.1) (Prod.snd p.1) p.2)
      prepared (encList encBits) := by
    dsimp only [prepared]
    fun_prop
  obtain ⟨d, _, hsplit⟩ := hsplit.exists_degree
  obtain ⟨l, hlen⟩ := hprep.length_le_time
  let budget (p : α × List Bool) := base p ^ max d 1
  have hbase (p : α × List Bool) : 1 ≤ base p := by dsimp only [base]; omega
  have hbase_le (p : α × List Bool) : base p ≤ budget p := by
    exact Nat.le_self_pow (by omega : max d 1 ≠ 0) _
  have hpow (p : α × List Bool) : base p ^ d ≤ budget p :=
    Nat.pow_le_pow_right (by have := hbase p; omega) (le_max_left d 1)
  have hrows₀ := hsplit.inO.comp hprep
  have hrows : ∃ S, ComputableInO rows input (encList encBits) budget S := by
    refine ⟨_, (hrows₀.mono_time (1 + (l + 1) ^ d) (fun p => ?_)).of_enc_eq
      (fun _ => rfl)⟩
    · have hp := hlen p
      have hsize : (prepared (prep p)).length + 1 ≤ (l + 1) * base p := by
        have hb := hbase p
        dsimp only [base] at hb ⊢
        rw [Nat.add_mul, Nat.one_mul]
        have heq : Ttr p + Tw p + (input p).length + 1 =
            (input p).length + Ttr p + Tw p + 1 := by omega
        rw [heq] at hp
        omega
      have hs := (Nat.pow_le_pow_left hsize d)
      rw [Nat.mul_pow] at hs
      have hs' := hs.trans (Nat.mul_le_mul_left _ (hpow p))
      have ht : Ttr p + Tw p + (input p).length ≤ budget p := by
        have := hbase_le p
        dsimp only [base] at this
        omega
      change Ttr p + Tw p + (input p).length + ((prepared (prep p)).length + 1) ^ d ≤ _
      calc
        _ ≤ budget p + (l + 1) ^ d * budget p := Nat.add_le_add ht hs'
        _ ≤ (1 + (l + 1) ^ d) * (budget p + 1) := by
          rw [Nat.add_mul, Nat.one_mul]
          exact Nat.add_le_add (by omega) (Nat.mul_le_mul_left _ (by omega))
  obtain ⟨Srows, hrows⟩ := hrows
  obtain ⟨m, hm⟩ := hrows.length_le_time
  have hmap := ComputableInO.mapWith hV (ComputableInO.fst enc encBits) hrows
  refine ⟨max d 1, _, (hmap.mono_time (4 + 2 * m) (fun p => ?_)).of_enc_eq
    (fun _ => rfl)⟩
  let out := (encList encOut (repeatOutputs (trials p) (width p) V p)).length
  have hi : (input p).length ≤ budget p := by
    have := hbase_le p
    dsimp only [base] at this
    omega
  have hp : (enc p.1).length ≤ budget p :=
    (by simp only [input, length_encPair]; omega : (enc p.1).length ≤ (input p).length).trans hi
  have hb : 1 ≤ budget p := (hbase p).trans (hbase_le p)
  have hlen : (encList encBits (rows p)).length ≤ (2 * m) * budget p := by
    calc
      _ ≤ m * (budget p + 1) := hm p
      _ ≤ m * (2 * budget p) := Nat.mul_le_mul_left _ (by omega)
      _ = (2 * m) * budget p := by ring
  have hr : listMax (fun row => Tv (p.1, row)) (rows p) ≤ R p := by
    apply listMax_le
    intro row hrow
    exact hR p row (BitString.length_of_mem_listRows hrow)
  change (input p).length + (input p).length + budget p + ((rows p).length + 1) *
    ((enc p.1).length + (encList encBits (rows p)).length + out +
      listMax (fun row => Tv (p.1, row)) (rows p)) ≤ _
  rw [show (rows p).length = trials p by simp [rows]]
  let bound := budget p + out + R p
  have hround : (enc p.1).length + (encList encBits (rows p)).length + out +
      listMax (fun row => Tv (p.1, row)) (rows p) ≤ (1 + 2 * m) * bound := by
    calc
      _ ≤ budget p + (2 * m) * budget p + out + R p :=
        Nat.add_le_add (Nat.add_le_add_right (Nat.add_le_add hp hlen) out) hr
      _ = (1 + 2 * m) * budget p + (out + R p) := by ring
      _ ≤ (1 + 2 * m) * bound := by
        dsimp only [bound]
        rw [Nat.add_assoc, Nat.mul_add]
        exact Nat.add_le_add_left (Nat.le_mul_of_pos_left _ (by omega)) _
  have hstart : (input p).length + (input p).length + budget p ≤
      (trials p + 1) * (3 * bound) :=
    (by dsimp only [bound]; omega : (input p).length + (input p).length + budget p ≤ 3 * bound).trans
      (Nat.le_mul_of_pos_left _ (by omega))
  calc
    _ ≤ (trials p + 1) * (3 * bound) + (trials p + 1) * ((1 + 2 * m) * bound) :=
      Nat.add_le_add hstart (Nat.mul_le_mul_left _ hround)
    _ = (4 + 2 * m) * ((trials p + 1) * bound) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.le_succ _)

/-- Vote collection charges polynomial overhead for the input and the unary dimensions and
at most one verifier call per row. Votes are returned using the raw bit-list encoding. -/
theorem computableInO_repeatVotes {enc : α ↪ List Bool}
    {V : α × List Bool → Bool} {trials width : α × List Bool → ℕ}
    {Tv Sv Ttr Str Tw Sw R : α × List Bool → ℕ}
    (hV : ComputableInO V (encPair enc encBits) encBool Tv Sv)
    (htr : ComputableInO trials (encPair enc encBits) encUnary Ttr Str)
    (hw : ComputableInO width (encPair enc encBits) encUnary Tw Sw)
    (hR : ∀ p row, row.length = width p → Tv (p.1, row) ≤ R p) :
    ∃ d S, ComputableInO (fun p => repeatVotes (trials p) (width p) V p)
      (encPair enc encBits) encBits
      (fun p => (trials p + 1) * (((encPair enc encBits p).length + Ttr p + Tw p + 1) ^ d + R p))
      S := by
  obtain ⟨d, _, hout⟩ := computableInO_repeatOutputs hV htr hw hR
  obtain ⟨m, hm⟩ := htr.length_le_time
  have hbits := (ComputableInDegree.listToBits.inO_one).comp_linear hout
  refine ⟨max d 1, _, (hbits.mono_time (3 * m + 1) (fun p => ?_)).of_enc_eq (fun _ => rfl)⟩
  let base := (encPair enc encBits p).length + Ttr p + Tw p + 1
  let budget := base ^ max d 1
  have hbase : base ≤ budget := Nat.le_self_pow (by omega : max d 1 ≠ 0) _
  have hpow : base ^ d ≤ budget :=
    Nat.pow_le_pow_right (by dsimp only [base]; omega) (le_max_left d 1)
  have htrials : trials p ≤ m * budget := by
    have h := hm p
    rw [encUnary_apply, List.length_replicate] at h
    exact h.trans (Nat.mul_le_mul_left _ ((by dsimp only [base]; omega :
      Ttr p + 1 ≤ base).trans hbase))
  have houtlen : (encList encBool (repeatOutputs (trials p) (width p) V p)).length ≤
      3 * trials p := by
    simpa only [length_repeatOutputs, Nat.mul_comm] using
      length_encList_le encBool (repeatOutputs (trials p) (width p) V p) (b := 1)
        (fun v _ => by cases v <;> decide)
  change (trials p + 1) *
    (base ^ d + (encList encBool (repeatOutputs (trials p) (width p) V p)).length + R p) ≤ _
  calc
    _ ≤ (trials p + 1) * (budget + 3 * (m * budget) + R p) :=
      Nat.mul_le_mul_left _ (Nat.add_le_add_right
        (Nat.add_le_add hpow (houtlen.trans (Nat.mul_le_mul_left 3 htrials))) _)
    _ ≤ (trials p + 1) * ((3 * m + 1) * (budget + R p)) := by
      apply Nat.mul_le_mul_left
      rw [Nat.mul_add]
      calc
        _ = (3 * m + 1) * budget + R p := by ring
        _ ≤ _ := Nat.add_le_add_left (Nat.le_mul_of_pos_left _ (by omega)) _
    _ = (3 * m + 1) * ((trials p + 1) * (budget + R p)) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.le_succ _)

/-- The strict majority of `2 r(n)` runs of `V`, where `n` is the length of the encoded instance:
the random string is cut into `2 r(n)` rows of `p(n)` bits (`Cslib.BitString.listRows`), `V` runs
on each row, and the answer is `true` when more than `r(n)` runs accept. Bits missing from a short
random string read as `false`. -/
def repeatMajority (enc : α ↪ List Bool) (r p : Polynomial ℕ) (V : α × List Bool → Bool)
    (x : α × List Bool) : Bool :=
  decide (r.eval (enc x.1).length <
    (repeatVotes (2 * r.eval (enc x.1).length) (p.eval (enc x.1).length) V x).countP id)

variable {enc : α ↪ List Bool}

/-- Majority votes of a polynomial-time decider take polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_repeatMajority {V : α × List Bool → Bool}
    (hV : ComputableInPolyTime V (encPair enc encBits) encBool) (r p : Polynomial ℕ) :
    ComputableInPolyTime (repeatMajority enc r p V) (encPair enc encBits) encBool := by
  fun_prop [repeatMajority]

/-- On a random string of `2 r(n)` rows of `p(n)` bits, the majority vote compares the number of
accepting rows with `r(n)`. -/
theorem repeatMajority_ofFn {r p : Polynomial ℕ} {V : α × List Bool → Bool} (a : α)
    (x : BitString (2 * r.eval (enc a).length * p.eval (enc a).length)) :
    repeatMajority enc r p V (a, List.ofFn x) = decide (r.eval (enc a).length <
      (univ.filter fun i => V (a, List.ofFn (BitString.block x i)) = true).card) := by
  rw [repeatMajority, repeatVotes_ofFn, List.countP_ofFn]
  rfl

/-- The disjunction of `q(n)` runs of `V`, where `n` is the length of the encoded instance: the
random string is cut into `q(n)` rows of `p(n)` bits (`Cslib.BitString.listRows`), `V` runs on each
row, and the answer is `true` when some run accepts. Bits missing from a short random string read
as `false`. -/
def repeatAny (enc : α ↪ List Bool) (q p : Polynomial ℕ) (V : α × List Bool → Bool)
    (x : α × List Bool) : Bool :=
  (repeatVotes (q.eval (enc x.1).length) (p.eval (enc x.1).length) V x).any id

variable {enc : α ↪ List Bool}

/-- Repeating a polynomial-time decider takes polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_repeatAny {V : α × List Bool → Bool}
    (hV : ComputableInPolyTime V (encPair enc encBits) encBool) (q p : Polynomial ℕ) :
    ComputableInPolyTime (repeatAny enc q p V) (encPair enc encBits) encBool := by
  fun_prop [repeatAny]

/-- On a random string of `q(n)` rows of `p(n)` bits, the repetition accepts when some row is
accepted. -/
theorem repeatAny_ofFn_eq_true_iff {q p : Polynomial ℕ} {V : α × List Bool → Bool} (a : α)
    (x : BitString (q.eval (enc a).length * p.eval (enc a).length)) :
    repeatAny enc q p V (a, List.ofFn x) = true ↔
      ∃ i, V (a, List.ofFn (BitString.block x i)) = true := by
  simp [repeatAny, repeatVotes_ofFn, List.any_eq_true, List.mem_ofFn]

end Cslib.Complexity
